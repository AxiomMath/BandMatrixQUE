module

public import BlockBand.Layers.DiffCovarianceNoise

/-!
# The differentiated conditional covariance

The differentiated-covariance lemma: its statement is `DiffCovarianceStatement`, proved by
`diffCovariance_holds` from `ConditionalBlockGUECount`, `GaussianLpGradient` and
`WeightedLayerContract` (only its `moments` field is used).

Proof (Steps 1–6).
1. **Step 1** (`dcv_hasDerivAt_resolvent`, `DiffCovarianceFactors`): `𝒢(h)⁻¹ = 𝒢⁻¹ + hŜ`
   exactly, so `𝒢̇ = -𝒢Ŝ𝒢`.
2. **Derivative of the covariance** (§4, `dcv_hasDerivAt_cov`). The second-order resolvent
   identity `𝒢(h) - 𝒢 - h𝒢̇ = h² 𝒢(h)Ŝ𝒢Ŝ𝒢` and the uniform moments of the Gaussian absorption lemma
   (`X - hS` is Hermitian for every real `h`) give the derivative of
   `h ↦ Cov(g(h), 𝒢(h))` at `0`: `Cov(ġ, 𝒢) + Cov(g, 𝒢̇)` (`dcvCovDir`). This is the
   product-rule form of the four-term formula of Step 3; no cutoff is needed because the
   remainder is controlled by `E‖𝒢(h)‖⁴` uniformly in `|h| ≤ 1`.
3. **Steps 2–4** (§1–3). Each covariance is written by the Ornstein–Uhlenbeck identity
   (`ou_covariance_matrix`) for the regularized resolvent `G_κ = (𝒢⁻¹ + iκ)⁻¹`
   (`dcv_cov_generic`); the derivatives carry exactly one insertion `G_κ P G_κ`, which is bounded
   through the factorization `‖G P G‖ ≤ s Θ(G)²` (the covariance factorization, `dcv_factor_le`; `s = ‖Y‖`
   for `P = Ŝ`, `s = ‖Y‖ + ‖D₀‖` for `P = Ŝ + D₀`); the contraction lemma `tcv_contract_le`
   (`‖𝒱(K)‖ ≤ 10‖K‖/W`), AM–GM across the two OU samples (`tcv_pow_mul_le`) and `x_t ∼ μ`
   (`tcv_integral_interp`) give `‖Cov(ġ_κ, G_κ) + Cov(g_κ, -G_κPG_κ)‖ ≤ 80 s W⁻² E Θ(G_κ)⁵`
   (`dcv_cov_fixed`).
4. **Step 6** (§3, `dcv_cov_core`): `κ → 0` by dominated convergence (`Θ(G_κ) ≤ 2Θ(𝒢)` a.s.,
   majorants `C ‖P‖ Θ(𝒢)³`); with `‖Θ(𝒢)‖_5 ≤ C_Θ` (`dcv_theta_eLpNorm`):
   `‖Cov(ġ, 𝒢) + Cov(g, 𝒢̇)‖ ≤ 2560 s C_Θ⁵ / W²`.
5. **Step 5** (`DiffCovarianceNoise`): the derivative-noise bound.
6. `‖Y‖ ≤ Tr Y = W u` and `‖Y‖_HS ≤ Tr Y` for `Y ⪰ 0` (`dcv_Y_bounds`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix WithLp Filter Topology Asymptotics
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm GaussianLpGradient
  ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 0. The covariance and its directional derivative
-/

/-- The trace–matrix covariance `Cov(g, U) = E(g U) - (E g)(E U)` (entrywise expectations). -/
def dcvCov {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℂ)
    (U : Ω → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  matrixExpect μ (fun ω => g ω • U ω) - (∫ ω, g ω ∂μ) • matrixExpect μ U

/-- **The differentiated covariance** along a direction `P` of `𝒢⁻¹`:
`Cov(ġ, 𝒢) + Cov(g, 𝒢̇)` with `g = W⁻¹ Tr(D 𝒢)`, `𝒢̇ = -𝒢 P 𝒢`, `ġ = -W⁻¹ Tr(D 𝒢 P 𝒢)`. For
`P = Ŝ` it is `∂_h Cov(g, 𝒢)` at `h = 0` (`dcv_hasDerivAt_cov_layer`); it is linear in `P`, and
`P = Ŝ + D₀` is "a bounded deterministic insertion added to `Ŝ`". -/
def dcvCovDir {W : ℕ} {σ : LayerShape} (μ : Measure (LayerSample W σ))
    (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (G : LayerSample W σ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  dcvCov μ (fun ω => -((W : ℂ)⁻¹ * (D * (G ω * P * G ω)).trace)) G +
    dcvCov μ (fun ω => (W : ℂ)⁻¹ * (D * G ω).trace) (fun ω => -(G ω * P * G ω))

/-!
## 1. The OU covariance bound for one pair of regularized observables
-/

section Generic

variable {W : ℕ} {b : ℝ} {σ : LayerShape}

/-- **Generic covariance bound** (Steps 2–4 for one pair, in the real coordinates): if
`∂_v f = W⁻¹ Tr(Σⱼ aⱼ (Λv) cⱼ)` with `‖aⱼ‖‖cⱼ‖ ≤ c_f Θ^{n_f}` and `∂_v U = Σₖ a'ₖ (Λv) c'ₖ` with
`‖a'ₖ‖‖c'ₖ‖ ≤ c_U Θ^{n_U}` (`Θ` continuous, bounded, nonnegative), then
`‖E(fU) - Ef EU‖ ≤ (10 ℓ_f ℓ_U c_f c_U / W²) · 2 E Θ^{n_f + n_U}`. -/
theorem dcv_cov_generic (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {f : (TflCoord W σ → ℝ) → ℂ}
    {U : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hf : ContDiff ℝ 1 f) (hU : ContDiff ℝ 1 U) {Cf Cf' CU CU' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf')
    (hUC : ∀ x, ‖U x‖ ≤ CU) (hU'C : ∀ x, ‖fderiv ℝ U x‖ ≤ CU')
    {Θ : (TflCoord W σ → ℝ) → ℝ} (hΘc : Continuous Θ) (hΘ0 : ∀ x, 0 ≤ Θ x) {CΘ : ℝ}
    (hΘC : ∀ x, Θ x ≤ CΘ) {ℓf ℓU nf nU : ℕ} {cf cU : ℝ} (hcf : 0 ≤ cf) (hcU : 0 ≤ cU)
    (hfr : ∀ x, ∃ a c : Fin ℓf → Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      (∀ v, fderiv ℝ f x v = (W : ℂ)⁻¹ * (∑ j, a j * tcvLam W b σ v * c j).trace) ∧
        ∀ j, ‖a j‖ * ‖c j‖ ≤ cf * Θ x ^ nf)
    (hUr : ∀ y, ∃ a c : Fin ℓU → Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      (∀ v, fderiv ℝ U y v = ∑ k, a k * tcvLam W b σ v * c k) ∧
        ∀ k, ‖a k‖ * ‖c k‖ ≤ cU * Θ y ^ nU) :
    ‖(∫ x, f x • U x ∂gaussianProduct (tflVar W b σ)) -
        (∫ x, f x ∂gaussianProduct (tflVar W b σ)) •
          (∫ x, U x ∂gaussianProduct (tflVar W b σ))‖ ≤
      10 * ℓf * ℓU * cf * cU / (W : ℝ) ^ 2 *
        (2 * ∫ x, Θ x ^ (nf + nU) ∂gaussianProduct (tflVar W b σ)) := by
  set v := tflVar W b σ with hv
  set μ := gaussianProduct v with hμ
  set n := nf + nU with hn
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set c₀ : ℝ := 10 * ℓf * ℓU * cf * cU / (W : ℝ) ^ 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  have hker : ∀ x y : TflCoord W σ → ℝ,
      ‖∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f x (Pi.single i 1)) • fderiv ℝ U y (Pi.single i 1)‖ ≤
        c₀ * (Θ x ^ n + Θ y ^ n) := by
    intro x y
    obtain ⟨a, c, hTfv, hacf⟩ := hfr x
    obtain ⟨a', c', hTUv, hacU⟩ := hUr y
    have e1 : ∀ i, fderiv ℝ f x (Pi.single i 1) =
        (W : ℂ)⁻¹ * (∑ j, a j * tcvLam W b σ (Pi.single i 1) * c j).trace := fun i => hTfv _
    have e2 : ∀ i, fderiv ℝ U y (Pi.single i 1) =
        ∑ k, a' k * tcvLam W b σ (Pi.single i 1) * c' k := fun i => hTUv _
    simp_rw [e1, e2]
    rw [tcv_kernel_eq]
    have hk := tcv_kernel_le σ hW hb0 hb1 a c a' c' (Bf := cf * Θ x ^ nf)
      (BU := cU * Θ y ^ nU) (mul_nonneg hcf (pow_nonneg (hΘ0 x) _)) hacf hacU
    refine hk.trans ?_
    have hamgm := tcv_pow_mul_le (hΘ0 x) (hΘ0 y) nf nU
    calc 10 * ℓf * ℓU * (cf * Θ x ^ nf) * (cU * Θ y ^ nU) / (W : ℝ) ^ 2
        = c₀ * (Θ x ^ nf * Θ y ^ nU) := by rw [hc₀]; ring
      _ ≤ c₀ * (Θ x ^ n + Θ y ^ n) := mul_le_mul_of_nonneg_left hamgm hc₀0
  set I : ℝ := ∫ x, Θ x ^ n ∂μ with hI
  have hpc : Continuous (fun x => Θ x ^ n) := hΘc.pow n
  have hCΘ0 : 0 ≤ CΘ := (hΘ0 0).trans (hΘC 0)
  have hpowle : ∀ x, ‖Θ x ^ n‖ ≤ CΘ ^ n := fun x => by
    rw [Real.norm_of_nonneg (pow_nonneg (hΘ0 x) _)]
    exact pow_le_pow_left₀ (hΘ0 x) (hΘC x) n
  have hkt : ∀ t : ℝ, 0 < t →
      ‖∫ p, ∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ U (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂μ.prod μ‖ ≤ c₀ * (2 * I) := by
    intro t ht
    set y : (TflCoord W σ → ℝ) × (TflCoord W σ → ℝ) → (TflCoord W σ → ℝ) :=
      fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2 with hy
    have hyc : Continuous y := by fun_prop
    have hA : Integrable (fun p : (TflCoord W σ → ℝ) × (TflCoord W σ → ℝ) => Θ p.1 ^ n)
        (μ.prod μ) :=
      ou_integrable_bdd v (hpc.comp continuous_fst) (C := CΘ ^ n) fun p => hpowle p.1
    have hB : Integrable (fun p : (TflCoord W σ → ℝ) × (TflCoord W σ → ℝ) => Θ (y p) ^ n)
        (μ.prod μ) :=
      ou_integrable_bdd v (hpc.comp hyc) (C := CΘ ^ n) fun p => hpowle (y p)
    have hbd := norm_integral_le_of_norm_le ((hA.add hB).const_mul c₀)
      (Eventually.of_forall fun p => hker p.1 (y p))
    refine hbd.trans (le_of_eq ?_)
    rw [integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add hA hB, integral_fun_fst (fun x => Θ x ^ n),
      probReal_univ, one_smul, tcv_integral_interp v hpc ht.le]
    ring
  rw [ou_covariance_matrix v hf hfC hf'C hU hUC hU'C]
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t) * (c₀ * (2 * I))) (Set.Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).mul_const _
  refine (norm_integral_le_of_norm_le hexp ?_).trans (le_of_eq ?_)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (hkt t ht) (Real.exp_pos _).le
  · rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]

end Generic

/-!
## 2. The two covariances at a fixed regularization `κ > 0`
-/

section FixedKappa

variable (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
  (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)

/-- `‖A Λv B‖ ≤ ‖A‖ ‖B‖ ‖Λ‖ ‖v‖`. -/
theorem dcv_sandwich_lam_le (A B : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (v : TflCoord W σ → ℝ) :
    ‖A * tcvLam W b σ v * B‖ ≤ ‖A‖ * ‖B‖ * ‖tcvLam W b σ‖ * ‖v‖ := by
  have h1 : ‖A * tcvLam W b σ v * B‖ ≤ ‖A‖ * ‖tcvLam W b σ v‖ * ‖B‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have h2 := (tcvLam W b σ).le_opNorm v
  calc _ ≤ ‖A‖ * ‖tcvLam W b σ v‖ * ‖B‖ := h1
    _ ≤ ‖A‖ * (‖tcvLam W b σ‖ * ‖v‖) * ‖B‖ := by gcongr
    _ = ‖A‖ * ‖B‖ * ‖tcvLam W b σ‖ * ‖v‖ := by ring

/-- `‖A P B‖ ≤ ‖A‖ ‖P‖ ‖B‖`. -/
theorem dcv_norm_mul3_le (A P B : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    ‖A * P * B‖ ≤ ‖A‖ * ‖P‖ * ‖B‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

variable {W} in
/-- `|W⁻¹ Tr(D A (Λv) B)| ≤ 4 ‖D‖ ‖A‖ ‖B‖ ‖Λ‖ ‖v‖`. -/
theorem dcv_tr_sandwich_le (hW : 0 < W) (D A B : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (Λ : (TflCoord W σ → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (v : TflCoord W σ → ℝ) :
    ‖(W : ℂ)⁻¹ * (D * (A * Λ v * B)).trace‖ ≤ 4 * (‖D‖ * ‖A‖ * ‖B‖ * ‖Λ‖) * ‖v‖ := by
  rw [← tcvTr_apply]
  refine (tcv_tr_le σ hW _).trans ?_
  have h1 : ‖D * (A * Λ v * B)‖ ≤ ‖D‖ * (‖A‖ * ‖Λ v‖ * ‖B‖) :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (dcv_norm_mul3_le W σ _ _ _)
      (norm_nonneg _))
  have h2 := Λ.le_opNorm v
  have h3 : ‖A‖ * ‖Λ v‖ * ‖B‖ ≤ ‖A‖ * (‖Λ‖ * ‖v‖) * ‖B‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) (norm_nonneg _)
  calc 4 * ‖D * (A * Λ v * B)‖ ≤ 4 * (‖D‖ * (‖A‖ * ‖Λ v‖ * ‖B‖)) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ 4 * (‖D‖ * (‖A‖ * (‖Λ‖ * ‖v‖) * ‖B‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

theorem dcv_tr_sandwich_bound {d a c k l v : ℝ} (hd : 0 ≤ d) (ha0 : 0 ≤ a) (ha : a ≤ k)
    (hc0 : 0 ≤ c) (hc : c ≤ k) (hl : 0 ≤ l) (hv : 0 ≤ v) :
    4 * (d * a * c * l) * v ≤ 4 * (d * k * k * l) * v := by
  have hk : 0 ≤ k := ha0.trans ha
  have h1 : d * a * c ≤ d * k * k :=
    mul_le_mul (mul_le_mul_of_nonneg_left ha hd) hc hc0 (mul_nonneg hd hk)
  have h2 := mul_le_mul_of_nonneg_right h1 hl
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) hv

variable {W b X} in
/-- The first covariance at fixed `κ`: `‖Cov(f₁, G_κ)‖ ≤ 40 s W⁻² E Θ(G_κ)⁵`,
`f₁ = -W⁻¹ Tr(D G_κ P G_κ)`. -/
theorem dcv_cov_fixed_one (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    (hz : 0 ≤ z.im) {D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hD : ‖D‖ ≤ 1)
    (P Kh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {s : ℝ} (hs : 0 ≤ s)
    (hP : ∀ G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖G * P * G‖ ≤ s * dcvTheta Kh G ^ 2)
    {κ : ℝ} (hκ : 0 < κ) :
    ‖(∫ x, dcvF W b σ E z X D P κ x • tcvG W b σ E z X κ x ∂gaussianProduct (tflVar W b σ)) -
        (∫ x, dcvF W b σ E z X D P κ x ∂gaussianProduct (tflVar W b σ)) •
          (∫ x, tcvG W b σ E z X κ x ∂gaussianProduct (tflVar W b σ))‖ ≤
      10 * (2 : ℕ) * (1 : ℕ) * s * 1 / (W : ℝ) ^ 2 *
        (2 * ∫ x, dcvTheta Kh (tcvG W b σ E z X κ x) ^ (3 + 2) ∂gaussianProduct (tflVar W b σ)) := by
  set G := tcvG W b σ E z X κ with hGdef
  set Λ := tcvLam W b σ with hΛ
  have hGc : ContDiff ℝ 1 G := tcv_G_contDiff W b σ E z hX hz hκ
  have hGle : ∀ x, ‖G x‖ ≤ κ⁻¹ := tcv_G_le W b σ E z hX hz hκ
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hD0 := norm_nonneg D
  have hP0 := norm_nonneg P
  have hΛ0 := norm_nonneg Λ
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : (TflCoord W σ → ℝ) → ℝ, Θ = fun x => dcvTheta Kh (G x) :=
    ⟨_, rfl⟩
  have hΘx : ∀ x, Θ x = dcvTheta Kh (G x) := fun x => by rw [hΘdef]
  have hΘc : Continuous Θ := by rw [hΘdef]; exact (dcv_continuous_theta Kh).comp hGc.continuous
  have hΘ0 : ∀ x, 0 ≤ Θ x := fun x => by rw [hΘx]; exact dcvTheta_nonneg Kh (G x)
  have hΘC : ∀ x, Θ x ≤ κ⁻¹ + κ⁻¹ * ‖Khᴴ‖ + ‖Kh‖ * κ⁻¹ := fun x => by
    have h1 : ‖G x * Khᴴ‖ ≤ κ⁻¹ * ‖Khᴴ‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hGle x) (norm_nonneg _))
    have h2 : ‖Kh * G x‖ ≤ ‖Kh‖ * κ⁻¹ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hGle x) (norm_nonneg _))
    rw [hΘx, dcvTheta]
    linarith [hGle x]
  have hI : ∫ x, dcvTheta Kh (tcvG W b σ E z X κ x) ^ (3 + 2) ∂gaussianProduct (tflVar W b σ) =
      ∫ x, Θ x ^ (3 + 2) ∂gaussianProduct (tflVar W b σ) := by rw [hΘdef]
  rw [hI]
  have hGΘ : ∀ x, ‖G x‖ ≤ Θ x := fun x => by rw [hΘx]; exact dcv_norm_le_theta Kh (G x)
  have hTΘ : ∀ x, ‖G x * P * G x‖ ≤ s * Θ x ^ 2 := fun x => by rw [hΘx]; exact hP (G x)
  have hTle : ∀ x, ‖G x * P * G x‖ ≤ κ⁻¹ * ‖P‖ * κ⁻¹ := fun x =>
    (dcv_norm_mul3_le W σ _ _ _).trans (by gcongr <;> exact hGle x)
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  -- derivative of `G`
  have hGd : ∀ x v, fderiv ℝ G x v = -(G x * Λ v * G x) := fun x v => by
    obtain ⟨T, hT, hTv⟩ := tcv_G_hasFDerivAt W b σ E z hX hz hκ x
    rw [hT.fderiv, hTv]
  -- derivative of `-G P G`
  have hUd : ∀ x v, fderiv ℝ (fun y => -(G y * P * G y)) x v =
      G x * Λ v * (G x * P * G x) + (G x * P * G x) * Λ v * G x := fun x v => by
    obtain ⟨T, hT, hTv⟩ := dcv_T_hasFDerivAt W b σ E z hX hz hκ P x
    have h2 : HasFDerivAt (fun y => -(G y * P * G y)) (-T) x := hT.neg
    rw [h2.fderiv, _root_.neg_apply, hTv, neg_neg]
  have hTr : ∀ N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖(W : ℂ)⁻¹ * N.trace‖ ≤ 4 * ‖N‖ :=
    fun N => by rw [← tcvTr_apply]; exact tcv_tr_le σ hW N
  refine dcv_cov_generic hW hb0 hb1 (dcvF_contDiff W b σ E z hX hz D P hκ) hGc
    (Cf := 4 * ‖D‖ * (κ⁻¹ * ‖P‖ * κ⁻¹))
    (Cf' := 4 * (2 * (κ⁻¹ * ‖P‖ * κ⁻¹) * ‖D‖ * κ⁻¹) * ‖Λ‖) (CU := κ⁻¹)
    (CU' := κ⁻¹ * κ⁻¹ * ‖Λ‖) ?_ ?_ hGle ?_ hΘc hΘ0 hΘC (ℓf := 2) (ℓU := 1) (nf := 3) (nU := 2)
    hs zero_le_one ?_ ?_
  · intro x
    rw [dcvF, norm_neg]
    refine (dcv_traceCLM_le σ hW D _).trans ?_
    gcongr; exact hTle x
  · intro x
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [dcvF_fderiv W b σ E z hX hz D P hκ]
    refine (hTr _).trans ?_
    have hM : ‖(G x * P * G x) * D * G x + G x * D * (G x * P * G x)‖ ≤
        2 * (κ⁻¹ * ‖P‖ * κ⁻¹) * ‖D‖ * κ⁻¹ := by
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖(G x * P * G x) * D * G x‖ ≤ (κ⁻¹ * ‖P‖ * κ⁻¹) * ‖D‖ * κ⁻¹ :=
        (dcv_norm_mul3_le W σ _ _ _).trans (by gcongr; exacts [hTle x, hGle x])
      have h2 : ‖G x * D * (G x * P * G x)‖ ≤ (κ⁻¹ * ‖P‖ * κ⁻¹) * ‖D‖ * κ⁻¹ := by
        refine (dcv_norm_mul3_le W σ _ _ _).trans ?_
        calc ‖G x‖ * ‖D‖ * ‖G x * P * G x‖ ≤ κ⁻¹ * ‖D‖ * (κ⁻¹ * ‖P‖ * κ⁻¹) := by
              gcongr; exacts [hGle x, hTle x]
          _ = _ := by ring
      linarith
    have h3 : ‖((G x * P * G x) * D * G x + G x * D * (G x * P * G x)) * Λ v‖ ≤
        ‖(G x * P * G x) * D * G x + G x * D * (G x * P * G x)‖ * (‖Λ‖ * ‖v‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (Λ.le_opNorm v) (norm_nonneg _))
    calc 4 * ‖((G x * P * G x) * D * G x + G x * D * (G x * P * G x)) * Λ v‖
        ≤ 4 * (2 * (κ⁻¹ * ‖P‖ * κ⁻¹) * ‖D‖ * κ⁻¹ * (‖Λ‖ * ‖v‖)) := by
          gcongr; exact h3.trans (by gcongr)
      _ = _ := by ring
  · intro x
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hGd, norm_neg]
    refine (dcv_sandwich_lam_le W b σ _ _ v).trans ?_
    gcongr <;> exact hGle x
  · intro x
    refine ⟨![(G x * P * G x) * D * G x, G x * D * (G x * P * G x)], ![1, 1], fun v => ?_, ?_⟩
    · rw [dcvF_fderiv W b σ E z hX hz D P hκ, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.mul_one, Matrix.add_mul]
      rfl
    · have h1 : ‖(1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖ ≤ 1 := dcv_norm_one_le
      have hT := hTΘ x
      have hG := hGΘ x
      have hΘx := hΘ0 x
      have hsΘ : 0 ≤ s * Θ x ^ 2 := mul_nonneg hs (pow_nonneg hΘx _)
      have hb1' : ‖(G x * P * G x) * D * G x‖ ≤ s * Θ x ^ 3 := by
        refine (dcv_norm_mul3_le W σ _ _ _).trans ?_
        calc ‖G x * P * G x‖ * ‖D‖ * ‖G x‖ ≤ (s * Θ x ^ 2) * 1 * Θ x :=
              mul_le_mul (mul_le_mul hT hD hD0 hsΘ) hG (norm_nonneg _) (by linarith)
          _ = s * Θ x ^ 3 := by ring
      have hb2' : ‖G x * D * (G x * P * G x)‖ ≤ s * Θ x ^ 3 := by
        refine (dcv_norm_mul3_le W σ _ _ _).trans ?_
        calc ‖G x‖ * ‖D‖ * ‖G x * P * G x‖ ≤ Θ x * 1 * (s * Θ x ^ 2) :=
              mul_le_mul (mul_le_mul hG hD hD0 hΘx) hT (norm_nonneg _) (by linarith)
          _ = s * Θ x ^ 3 := by ring
      intro j
      fin_cases j
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        calc _ ≤ s * Θ x ^ 3 * 1 := mul_le_mul hb1' h1 (norm_nonneg _) (by positivity)
          _ = s * Θ x ^ 3 := by ring
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        calc _ ≤ s * Θ x ^ 3 * 1 := mul_le_mul hb2' h1 (norm_nonneg _) (by positivity)
          _ = s * Θ x ^ 3 := by ring
  · intro y
    refine ⟨![-(G y)], ![G y], fun v => ?_, ?_⟩
    · rw [hGd, Fin.sum_univ_one]
      simp only [Matrix.cons_val_zero, Matrix.neg_mul]
      rfl
    · intro k
      fin_cases k
      simp only [Fin.zero_eta, Matrix.cons_val_zero, norm_neg]
      have hG := hGΘ y
      calc ‖G y‖ * ‖G y‖ ≤ Θ y * Θ y := mul_le_mul hG hG (norm_nonneg _) (hΘ0 y)
        _ = 1 * Θ y ^ 2 := by ring

variable {W b X} in
/-- The second covariance at fixed `κ`: `‖Cov(f₂, -G_κ P G_κ)‖ ≤ 40 s W⁻² E Θ(G_κ)⁵`,
`f₂ = W⁻¹ Tr(D G_κ)`. -/
theorem dcv_cov_fixed_two (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    (hz : 0 ≤ z.im) {D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hD : ‖D‖ ≤ 1)
    (P Kh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {s : ℝ} (hs : 0 ≤ s)
    (hP : ∀ G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖G * P * G‖ ≤ s * dcvTheta Kh G ^ 2)
    {κ : ℝ} (hκ : 0 < κ) :
    ‖(∫ x, tflF W b σ E z X D κ x • -(tcvG W b σ E z X κ x * P * tcvG W b σ E z X κ x)
          ∂gaussianProduct (tflVar W b σ)) -
        (∫ x, tflF W b σ E z X D κ x ∂gaussianProduct (tflVar W b σ)) •
          (∫ x, -(tcvG W b σ E z X κ x * P * tcvG W b σ E z X κ x)
            ∂gaussianProduct (tflVar W b σ))‖ ≤
      10 * (1 : ℕ) * (2 : ℕ) * 1 * s / (W : ℝ) ^ 2 *
        (2 * ∫ x, dcvTheta Kh (tcvG W b σ E z X κ x) ^ (2 + 3) ∂gaussianProduct (tflVar W b σ)) := by
  set G := tcvG W b σ E z X κ with hGdef
  set Λ := tcvLam W b σ with hΛ
  have hGc : ContDiff ℝ 1 G := tcv_G_contDiff W b σ E z hX hz hκ
  have hGle : ∀ x, ‖G x‖ ≤ κ⁻¹ := tcv_G_le W b σ E z hX hz hκ
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hD0 := norm_nonneg D
  have hP0 := norm_nonneg P
  have hΛ0 := norm_nonneg Λ
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : (TflCoord W σ → ℝ) → ℝ, Θ = fun x => dcvTheta Kh (G x) :=
    ⟨_, rfl⟩
  have hΘx : ∀ x, Θ x = dcvTheta Kh (G x) := fun x => by rw [hΘdef]
  have hΘc : Continuous Θ := by rw [hΘdef]; exact (dcv_continuous_theta Kh).comp hGc.continuous
  have hΘ0 : ∀ x, 0 ≤ Θ x := fun x => by rw [hΘx]; exact dcvTheta_nonneg Kh (G x)
  have hΘC : ∀ x, Θ x ≤ κ⁻¹ + κ⁻¹ * ‖Khᴴ‖ + ‖Kh‖ * κ⁻¹ := fun x => by
    have h1 : ‖G x * Khᴴ‖ ≤ κ⁻¹ * ‖Khᴴ‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hGle x) (norm_nonneg _))
    have h2 : ‖Kh * G x‖ ≤ ‖Kh‖ * κ⁻¹ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hGle x) (norm_nonneg _))
    rw [hΘx, dcvTheta]
    linarith [hGle x]
  have hI : ∫ x, dcvTheta Kh (tcvG W b σ E z X κ x) ^ (2 + 3) ∂gaussianProduct (tflVar W b σ) =
      ∫ x, Θ x ^ (2 + 3) ∂gaussianProduct (tflVar W b σ) := by rw [hΘdef]
  rw [hI]
  have hGΘ : ∀ x, ‖G x‖ ≤ Θ x := fun x => by rw [hΘx]; exact dcv_norm_le_theta Kh (G x)
  have hTΘ : ∀ x, ‖G x * P * G x‖ ≤ s * Θ x ^ 2 := fun x => by rw [hΘx]; exact hP (G x)
  have hTle : ∀ x, ‖G x * P * G x‖ ≤ κ⁻¹ * ‖P‖ * κ⁻¹ := fun x =>
    (dcv_norm_mul3_le W σ _ _ _).trans (by gcongr <;> exact hGle x)
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  -- derivative of `G`
  have hGd : ∀ x v, fderiv ℝ G x v = -(G x * Λ v * G x) := fun x v => by
    obtain ⟨T, hT, hTv⟩ := tcv_G_hasFDerivAt W b σ E z hX hz hκ x
    rw [hT.fderiv, hTv]
  -- derivative of `-G P G`
  have hUd : ∀ x v, fderiv ℝ (fun y => -(G y * P * G y)) x v =
      G x * Λ v * (G x * P * G x) + (G x * P * G x) * Λ v * G x := fun x v => by
    obtain ⟨T, hT, hTv⟩ := dcv_T_hasFDerivAt W b σ E z hX hz hκ P x
    have h2 : HasFDerivAt (fun y => -(G y * P * G y)) (-T) x := hT.neg
    rw [h2.fderiv, _root_.neg_apply, hTv, neg_neg]
  have hTr : ∀ N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖(W : ℂ)⁻¹ * N.trace‖ ≤ 4 * ‖N‖ :=
    fun N => by rw [← tcvTr_apply]; exact tcv_tr_le σ hW N
  have hU2 : ContDiff ℝ 1 (fun x => -(G x * P * G x)) := ((hGc.mul contDiff_const).mul hGc).neg
  refine dcv_cov_generic hW hb0 hb1 (tflF_contDiff W b σ E z hX hz D hκ) hU2
    (Cf := 4 * ‖D‖ * κ⁻¹)
    (Cf' := 4 * (‖D‖ * κ⁻¹ * κ⁻¹ * ‖Λ‖)) (CU := κ⁻¹ * ‖P‖ * κ⁻¹)
    (CU' := 2 * (κ⁻¹ * (κ⁻¹ * ‖P‖ * κ⁻¹) * ‖Λ‖)) ?_ ?_ ?_ ?_ hΘc hΘ0 hΘC (ℓf := 1) (ℓU := 2)
    (nf := 2) (nU := 3) zero_le_one hs ?_ ?_
  · intro x
    refine (tflF_norm_le b σ E z X hW D κ x).trans ?_
    gcongr; exact hGle x
  · intro x
    have hC0 : 0 ≤ 4 * (‖D‖ * κ⁻¹ * κ⁻¹ * ‖Λ‖) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg hD0 hκi) hκi) hΛ0)
    refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun v => ?_
    rw [tflF_fderiv W b σ E z hX hz D hκ, norm_neg, ← tcvLam_apply]
    have hg : ‖Ring.inverse (tflPsi W b σ E z X κ x)‖ ≤ κ⁻¹ := tflPsi_inv_le W b σ E z hX hz hκ x
    exact (dcv_tr_sandwich_le σ hW D _ _ (tcvLam W b σ) v).trans
      (dcv_tr_sandwich_bound hD0 (norm_nonneg _) hg (norm_nonneg _) hg hΛ0 (norm_nonneg v))
  · intro x
    rw [norm_neg]; exact hTle x
  · intro x
    have hC0 : 0 ≤ 2 * (κ⁻¹ * (κ⁻¹ * ‖P‖ * κ⁻¹) * ‖Λ‖) :=
      mul_nonneg zero_le_two (mul_nonneg (mul_nonneg hκi (mul_nonneg (mul_nonneg hκi hP0) hκi))
        hΛ0)
    refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun v => ?_
    rw [hUd]
    refine (norm_add_le _ _).trans ?_
    have h1 := dcv_sandwich_lam_le W b σ (G x) (G x * P * G x) v
    have h2 := dcv_sandwich_lam_le W b σ (G x * P * G x) (G x) v
    have h3 : ‖G x‖ * ‖G x * P * G x‖ ≤ κ⁻¹ * (κ⁻¹ * ‖P‖ * κ⁻¹) := by
      gcongr; exacts [hGle x, hTle x]
    have h4 : ‖G x * P * G x‖ * ‖G x‖ ≤ κ⁻¹ * (κ⁻¹ * ‖P‖ * κ⁻¹) := by
      rw [mul_comm]; exact h3
    have hv := norm_nonneg v
    have h5 := mul_le_mul_of_nonneg_right h3 (mul_nonneg hΛ0 hv)
    have h6 := mul_le_mul_of_nonneg_right h4 (mul_nonneg hΛ0 hv)
    calc ‖G x * Λ v * (G x * P * G x)‖ + ‖G x * P * G x * Λ v * G x‖
        ≤ ‖G x‖ * ‖G x * P * G x‖ * (‖Λ‖ * ‖v‖) + ‖G x * P * G x‖ * ‖G x‖ * (‖Λ‖ * ‖v‖) := by
          refine add_le_add (h1.trans (le_of_eq ?_)) (h2.trans (le_of_eq ?_)) <;> ring
      _ ≤ κ⁻¹ * (κ⁻¹ * ‖P‖ * κ⁻¹) * (‖Λ‖ * ‖v‖) + κ⁻¹ * (κ⁻¹ * ‖P‖ * κ⁻¹) * (‖Λ‖ * ‖v‖) :=
          add_le_add h5 h6
      _ = 2 * (κ⁻¹ * (κ⁻¹ * ‖P‖ * κ⁻¹) * ‖Λ‖) * ‖v‖ := by ring
  · intro x
    refine ⟨![-(D * G x)], ![G x], fun v => ?_, ?_⟩
    · rw [tflF_fderiv W b σ E z hX hz D hκ, ← tcvLam_apply, Fin.sum_univ_one]
      simp only [Matrix.cons_val_zero, Matrix.neg_mul, trace_neg, mul_neg, Matrix.mul_assoc]
      rfl
    · intro j
      fin_cases j
      simp only [Fin.zero_eta, Matrix.cons_val_zero, norm_neg]
      have hG := hGΘ x
      have h1 : ‖D * G x‖ ≤ ‖G x‖ := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (G x)])
      calc ‖D * G x‖ * ‖G x‖ ≤ Θ x * Θ x := mul_le_mul (h1.trans hG) hG (norm_nonneg _) (hΘ0 x)
        _ = 1 * Θ x ^ 2 := by ring
  · intro y
    refine ⟨![G y, G y * P * G y], ![G y * P * G y, G y], fun v => ?_, ?_⟩
    · rw [hUd, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rfl
    · have hT := hTΘ y
      have hG := hGΘ y
      have hΘy := hΘ0 y
      have hb' : ‖G y‖ * ‖G y * P * G y‖ ≤ s * Θ y ^ 3 := by
        calc ‖G y‖ * ‖G y * P * G y‖ ≤ Θ y * (s * Θ y ^ 2) := by gcongr
          _ = s * Θ y ^ 3 := by ring
      intro k
      fin_cases k
      · simpa using hb'
      · simpa [mul_comm] using hb'

variable {W b X} in
/-- **The two covariances at fixed `κ`** (Steps 2–4): with `‖G P G‖ ≤ s Θ(G)²` for every `G` and
`‖D‖ ≤ 1`, `f₁ = -W⁻¹ Tr(D G_κ P G_κ)`, `f₂ = W⁻¹ Tr(D G_κ)`:
`‖Cov(f₁, G_κ) + Cov(f₂, -G_κ P G_κ)‖ ≤ 80 s W⁻² E Θ(G_κ)⁵`. -/
theorem dcv_cov_fixed (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    (hz : 0 ≤ z.im) {D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hD : ‖D‖ ≤ 1)
    (P Kh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {s : ℝ} (hs : 0 ≤ s)
    (hP : ∀ G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖G * P * G‖ ≤ s * dcvTheta Kh G ^ 2)
    {κ : ℝ} (hκ : 0 < κ) :
    ‖((∫ x, dcvF W b σ E z X D P κ x • tcvG W b σ E z X κ x ∂gaussianProduct (tflVar W b σ)) -
        (∫ x, dcvF W b σ E z X D P κ x ∂gaussianProduct (tflVar W b σ)) •
          (∫ x, tcvG W b σ E z X κ x ∂gaussianProduct (tflVar W b σ))) +
      ((∫ x, tflF W b σ E z X D κ x • -(tcvG W b σ E z X κ x * P * tcvG W b σ E z X κ x)
          ∂gaussianProduct (tflVar W b σ)) -
        (∫ x, tflF W b σ E z X D κ x ∂gaussianProduct (tflVar W b σ)) •
          (∫ x, -(tcvG W b σ E z X κ x * P * tcvG W b σ E z X κ x)
            ∂gaussianProduct (tflVar W b σ)))‖ ≤
      80 * s / (W : ℝ) ^ 2 *
        ∫ x, dcvTheta Kh (tcvG W b σ E z X κ x) ^ 5 ∂gaussianProduct (tflVar W b σ) := by
  refine (norm_add_le _ _).trans ?_
  have h1 := dcv_cov_fixed_one σ E z hW hb0 hb1 hX hz hD P Kh hs hP hκ
  have h2 := dcv_cov_fixed_two σ E z hW hb0 hb1 hX hz hD P Kh hs hP hκ
  have e : 80 * s / (W : ℝ) ^ 2 *
        ∫ x, dcvTheta Kh (tcvG W b σ E z X κ x) ^ 5 ∂gaussianProduct (tflVar W b σ) =
      10 * (2 : ℕ) * (1 : ℕ) * s * 1 / (W : ℝ) ^ 2 *
          (2 * ∫ x, dcvTheta Kh (tcvG W b σ E z X κ x) ^ (3 + 2) ∂gaussianProduct (tflVar W b σ)) +
        10 * (1 : ℕ) * (2 : ℕ) * 1 * s / (W : ℝ) ^ 2 *
          (2 * ∫ x, dcvTheta Kh (tcvG W b σ E z X κ x) ^ (2 + 3) ∂gaussianProduct (tflVar W b σ)) := by
    push_cast; ring_nf
  rw [e]
  exact add_le_add h1 h2

end FixedKappa

/-!
## 3. Step 6: removing the regularization, `κ → 0`
-/

section Limit

/-- Dominated convergence for a covariance `E(f U) - E f • E U`. -/
theorem dcv_cov_tendsto {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]
    [DecidableEq ι] {fm : ℕ → α → ℂ} {f : α → ℂ} {Um : ℕ → α → Matrix ι ι ℂ}
    {U : α → Matrix ι ι ℂ} {bf bU bfU : α → ℝ}
    (hfm : ∀ m, AEStronglyMeasurable (fm m) μ) (hUm : ∀ m, AEStronglyMeasurable (Um m) μ)
    (hbf : Integrable bf μ) (hbU : Integrable bU μ) (hbfU : Integrable bfU μ)
    (hf : ∀ m, ∀ᵐ x ∂μ, ‖fm m x‖ ≤ bf x) (hU : ∀ m, ∀ᵐ x ∂μ, ‖Um m x‖ ≤ bU x)
    (hfU : ∀ m, ∀ᵐ x ∂μ, ‖fm m x • Um m x‖ ≤ bfU x)
    (hlf : ∀ᵐ x ∂μ, Tendsto (fun m => fm m x) atTop (𝓝 (f x)))
    (hlU : ∀ᵐ x ∂μ, Tendsto (fun m => Um m x) atTop (𝓝 (U x))) :
    Tendsto (fun m => (∫ x, fm m x • Um m x ∂μ) - (∫ x, fm m x ∂μ) • ∫ x, Um m x ∂μ) atTop
      (𝓝 ((∫ x, f x • U x ∂μ) - (∫ x, f x ∂μ) • ∫ x, U x ∂μ)) := by
  have h1 : Tendsto (fun m => ∫ x, fm m x • Um m x ∂μ) atTop (𝓝 (∫ x, f x • U x ∂μ)) :=
    tendsto_integral_of_dominated_convergence bfU (fun m => (hfm m).smul (hUm m)) hbfU hfU
      (by filter_upwards [hlf, hlU] with x h1 h2; exact h1.smul h2)
  have h2 : Tendsto (fun m => ∫ x, fm m x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
    tendsto_integral_of_dominated_convergence bf hfm hbf hf hlf
  have h3 : Tendsto (fun m => ∫ x, Um m x ∂μ) atTop (𝓝 (∫ x, U x ∂μ)) :=
    tendsto_integral_of_dominated_convergence bU hUm hbU hU hlU
  exact h1.sub (h2.smul h3)

variable {W : ℕ} {b : ℝ} {σ : LayerShape}

/-- Transfer of a covariance from `layerLaw` to the real coordinates. -/
theorem dcv_cov_transfer {g : LayerSample W σ → ℂ}
    {U : LayerSample W σ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hg : Measurable g)
    (hU : Measurable U)
    (hUi : Integrable (fun x => U (tflEmbed W b σ x)) (gaussianProduct (tflVar W b σ)))
    (hgUi : Integrable (fun x => g (tflEmbed W b σ x) • U (tflEmbed W b σ x))
      (gaussianProduct (tflVar W b σ))) :
    dcvCov (layerLaw W b σ) g U =
      (∫ x, g (tflEmbed W b σ x) • U (tflEmbed W b σ x) ∂gaussianProduct (tflVar W b σ)) -
        (∫ x, g (tflEmbed W b σ x) ∂gaussianProduct (tflVar W b σ)) •
          ∫ x, U (tflEmbed W b σ x) ∂gaussianProduct (tflVar W b σ) := by
  have hΦ := tfl_measurable_embed W b σ
  unfold dcvCov
  have hgU : Measurable (fun ω => g ω • U ω) := hg.smul hU
  rw [tcv_matrixExpect_eq hgU hgUi, tcv_matrixExpect_eq hU hUi, tfl_layerLaw_eq_map,
    integral_map hΦ.aemeasurable hg.aestronglyMeasurable]

end Limit

section Core

variable {W : ℕ} {b : ℝ}

/-- **Steps 2–6 for one direction** (in `layerLaw` terms): with a.e. invertibility,
`‖G P G‖ ≤ s Θ(G)²` for every `G`, `‖D‖ ≤ 1` and `‖Θ(𝒢)‖_5 ≤ C_Θ`,
`‖Cov(ġ, 𝒢) + Cov(g, 𝒢̇)‖ ≤ 80 s W⁻² (32 C_Θ⁵)`, `𝒢̇ = -𝒢 P 𝒢`. -/
theorem dcv_cov_core (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (σ : LayerShape)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (E : ℝ) {z : ℂ}
    (hz : 0 ≤ z.im) {D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hD : ‖D‖ ≤ 1)
    (P Kh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {s : ℝ} (hs : 0 ≤ s)
    (hP : ∀ G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖G * P * G‖ ≤ s * dcvTheta Kh G ^ 2)
    (hinv : ∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det) {CT : ℝ} (hCT : 0 ≤ CT)
    (hmom : eLpNorm (fun ω => dcvTheta Kh (layerResolvent σ E z X ω)) (ENNReal.ofReal 5)
      (layerLaw W b σ) ≤ ENNReal.ofReal CT) :
    ‖dcvCovDir (layerLaw W b σ) D (fun ω => layerResolvent σ E z X ω) P‖ ≤
      80 * s / (W : ℝ) ^ 2 * (32 * CT ^ 5) := by
  set μ := gaussianProduct (tflVar W b σ) with hμ
  set Φ := tflEmbed W b σ with hΦdef
  have hΦ : Measurable Φ := tfl_measurable_embed W b σ
  have hlaw : layerLaw W b σ = μ.map Φ := tfl_layerLaw_eq_map W b σ
  have hGm : Measurable (fun ω => layerResolvent σ E z X ω) := measurable_layerResolvent σ E z X
  set Gr : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => layerResolvent σ E z X (Φ x) with hGrdef
  have hGr : Measurable Gr := hGm.comp hΦ
  have hinvμ : ∀ᵐ x ∂μ, IsUnit (layerMatrix σ E z X (Φ x)).det := by
    rw [hlaw] at hinv
    exact ae_of_ae_map hΦ.aemeasurable hinv
  set Θr : (TflCoord W σ → ℝ) → ℝ := fun x => dcvTheta Kh (Gr x) with hΘr
  have hΘrm : Measurable Θr := (dcv_continuous_theta Kh).measurable.comp hGr
  have hΘr0 : ∀ x, 0 ≤ Θr x := fun x => dcvTheta_nonneg Kh (Gr x)
  have hnΘ : ∀ x, ‖Θr x‖ = Θr x := fun x => Real.norm_of_nonneg (hΘr0 x)
  have hGΘ : ∀ x, ‖Gr x‖ ≤ Θr x := fun x => dcv_norm_le_theta Kh (Gr x)
  have hmomμ : eLpNorm Θr (ENNReal.ofReal 5) μ ≤ ENNReal.ofReal CT := by
    have hm : Measurable (fun ω => dcvTheta Kh (layerResolvent σ E z X ω)) :=
      (dcv_continuous_theta Kh).measurable.comp hGm
    rw [hlaw, eLpNorm_map_measure hm.aestronglyMeasurable hΦ.aemeasurable] at hmom
    exact hmom
  have hint : ∀ m : ℕ, 1 ≤ m → m ≤ 5 → Integrable (fun x => Θr x ^ m) μ := fun m h1 h5 => by
    have := dcv_integrable_pow hmomμ h1 (by exact_mod_cast h5)
    simpa only [hnΘ] using this
  have h5 : ∫ x, Θr x ^ 5 ∂μ ≤ CT ^ 5 := by
    have h := hmomμ
    rw [← eLpNorm_norm Θr hΘrm.aestronglyMeasurable,
      show (ENNReal.ofReal 5 : ℝ≥0∞) = ENNReal.ofReal ((5 : ℕ) : ℝ) by norm_num] at h
    have := (tcv_moment (G := Θr) (m := 5) (by norm_num) hCT h).2
    simpa only [hnΘ] using this
  -- the limit observables
  set φ1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ → ℂ :=
    fun N => -((W : ℂ)⁻¹ * (D * (N * P * N)).trace) with hφ1
  set φ2 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ → ℂ :=
    fun N => (W : ℂ)⁻¹ * (D * N).trace with hφ2
  set ψ2 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun N => -(N * P * N) with hψ2
  have hφ1c : Continuous φ1 :=
    (continuous_const.mul ((continuous_const.matrix_mul ((continuous_id.matrix_mul
      continuous_const).matrix_mul continuous_id)).matrix_trace)).neg
  have hφ2c : Continuous φ2 :=
    continuous_const.mul (continuous_const.matrix_mul continuous_id).matrix_trace
  have hψ2c : Continuous ψ2 :=
    ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id).neg
  have hP0 := norm_nonneg P
  have hTr : ∀ N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖(W : ℂ)⁻¹ * N.trace‖ ≤ 4 * ‖N‖ :=
    fun N => by rw [← tcvTr_apply]; exact tcv_tr_le σ hW N
  have hb1N : ∀ N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖φ1 N‖ ≤ 4 * ‖P‖ * ‖N‖ ^ 2 :=
    fun N => by
      simp only [hφ1, norm_neg]
      refine (hTr _).trans ?_
      have h1 : ‖D * (N * P * N)‖ ≤ ‖D‖ * (‖N‖ * ‖P‖ * ‖N‖) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (dcv_norm_mul3_le W σ _ _ _)
          (norm_nonneg _))
      have h2 : ‖D‖ * (‖N‖ * ‖P‖ * ‖N‖) ≤ 1 * (‖N‖ * ‖P‖ * ‖N‖) :=
        mul_le_mul_of_nonneg_right hD (by positivity)
      nlinarith
  have hb2N : ∀ N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖φ2 N‖ ≤ 4 * ‖N‖ := fun N => by
    simp only [hφ2]
    refine (hTr _).trans ?_
    have h1 : ‖D * N‖ ≤ ‖N‖ :=
      (norm_mul_le _ _).trans (by nlinarith [norm_nonneg N, norm_nonneg D])
    linarith
  have hc2N : ∀ N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖ψ2 N‖ ≤ ‖P‖ * ‖N‖ ^ 2 :=
    fun N => by
      simp only [hψ2, norm_neg]
      refine (dcv_norm_mul3_le W σ _ _ _).trans (le_of_eq ?_); ring
  -- domination for any `N` with `‖N‖ ≤ 2 Θ`
  have hdom : ∀ (N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (t : ℝ), ‖N‖ ≤ 2 * t →
      ‖φ1 N‖ ≤ 16 * ‖P‖ * t ^ 2 ∧ ‖N‖ ≤ 2 * t ∧ ‖φ1 N • N‖ ≤ 32 * ‖P‖ * t ^ 3 ∧
        ‖φ2 N‖ ≤ 8 * t ∧ ‖ψ2 N‖ ≤ 4 * ‖P‖ * t ^ 2 ∧ ‖φ2 N • ψ2 N‖ ≤ 32 * ‖P‖ * t ^ 3 := by
    intro N t hN
    have hN0 := norm_nonneg N
    have ht : 0 ≤ t := by linarith
    have hN2 : ‖N‖ ^ 2 ≤ (2 * t) ^ 2 := pow_le_pow_left₀ hN0 hN 2
    have e1 : ‖φ1 N‖ ≤ 16 * ‖P‖ * t ^ 2 := (hb1N N).trans (by nlinarith)
    have e4 : ‖φ2 N‖ ≤ 8 * t := (hb2N N).trans (by linarith)
    have e5 : ‖ψ2 N‖ ≤ 4 * ‖P‖ * t ^ 2 := (hc2N N).trans (by nlinarith)
    refine ⟨e1, hN, ?_, e4, e5, ?_⟩
    · rw [norm_smul]
      calc ‖φ1 N‖ * ‖N‖ ≤ (16 * ‖P‖ * t ^ 2) * (2 * t) :=
            mul_le_mul e1 hN hN0 (by positivity)
        _ = 32 * ‖P‖ * t ^ 3 := by ring
    · rw [norm_smul]
      calc ‖φ2 N‖ * ‖ψ2 N‖ ≤ (8 * t) * (4 * ‖P‖ * t ^ 2) :=
            mul_le_mul e4 e5 (norm_nonneg _) (by positivity)
        _ = 32 * ‖P‖ * t ^ 3 := by ring
  have hself : ∀ x, ‖Gr x‖ ≤ 2 * Θr x := fun x => by linarith [hGΘ x, hΘr0 x]
  -- integrability of the limit observables
  have hi2 := hint 2 (by norm_num) (by norm_num)
  have hi3 := hint 3 (by norm_num) (by norm_num)
  have hi1 : Integrable Θr μ := by simpa using hint 1 le_rfl (by norm_num)
  have hm1 : AEStronglyMeasurable (fun x => φ1 (Gr x)) μ :=
    (hφ1c.measurable.comp hGr).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun x => φ2 (Gr x)) μ :=
    (hφ2c.measurable.comp hGr).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun x => ψ2 (Gr x)) μ :=
    (hψ2c.measurable.comp hGr).aestronglyMeasurable
  have hF1 : Integrable (fun x => φ1 (Gr x)) μ :=
    Integrable.mono' (hi2.const_mul (16 * ‖P‖)) hm1
      (Eventually.of_forall fun x => (hdom _ _ (hself x)).1)
  have hU1 : Integrable Gr μ :=
    Integrable.mono' (hi1.const_mul 2) hGr.aestronglyMeasurable
      (Eventually.of_forall fun x => hself x)
  have hF1U1 : Integrable (fun x => φ1 (Gr x) • Gr x) μ :=
    Integrable.mono' (hi3.const_mul (32 * ‖P‖)) (hm1.smul hGr.aestronglyMeasurable)
      (Eventually.of_forall fun x => (hdom _ _ (hself x)).2.2.1)
  have hF2 : Integrable (fun x => φ2 (Gr x)) μ :=
    Integrable.mono' (hi1.const_mul 8) hm2
      (Eventually.of_forall fun x => (hdom _ _ (hself x)).2.2.2.1)
  have hU2 : Integrable (fun x => ψ2 (Gr x)) μ :=
    Integrable.mono' (hi2.const_mul (4 * ‖P‖)) hm3
      (Eventually.of_forall fun x => (hdom _ _ (hself x)).2.2.2.2.1)
  have hF2U2 : Integrable (fun x => φ2 (Gr x) • ψ2 (Gr x)) μ :=
    Integrable.mono' (hi3.const_mul (32 * ‖P‖)) (hm2.smul hm3)
      (Eventually.of_forall fun x => (hdom _ _ (hself x)).2.2.2.2.2)
  -- transfer to the coordinates
  have hdir : dcvCovDir (layerLaw W b σ) D (fun ω => layerResolvent σ E z X ω) P =
      ((∫ x, φ1 (Gr x) • Gr x ∂μ) - (∫ x, φ1 (Gr x) ∂μ) • ∫ x, Gr x ∂μ) +
        ((∫ x, φ2 (Gr x) • ψ2 (Gr x) ∂μ) - (∫ x, φ2 (Gr x) ∂μ) • ∫ x, ψ2 (Gr x) ∂μ) := by
    have e1 := dcv_cov_transfer (g := fun ω => φ1 (layerResolvent σ E z X ω))
      (U := fun ω => layerResolvent σ E z X ω) (hφ1c.measurable.comp hGm) hGm hU1 hF1U1
    have e2 := dcv_cov_transfer (g := fun ω => φ2 (layerResolvent σ E z X ω))
      (U := fun ω => ψ2 (layerResolvent σ E z X ω)) (hφ2c.measurable.comp hGm)
      (hψ2c.measurable.comp hGm) hU2 hF2U2
    show dcvCov (layerLaw W b σ) (fun ω => φ1 (layerResolvent σ E z X ω))
        (fun ω => layerResolvent σ E z X ω) +
      dcvCov (layerLaw W b σ) (fun ω => φ2 (layerResolvent σ E z X ω))
        (fun ω => ψ2 (layerResolvent σ E z X ω)) = _
    rw [e1, e2]
  rw [hdir]
  -- the regularized family `κ_m = 1/(m+1)`
  set κm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hκm
  have hκpos : ∀ m, 0 < κm m := fun m => by rw [hκm]; positivity
  have hκlim : Tendsto κm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Gm : ℕ → (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun m => tcvG W b σ E z X (κm m) with hGmdef
  have hGmc : ∀ m, Continuous (Gm m) := fun m =>
    (tcv_G_contDiff W b σ E z hX hz (hκpos m)).continuous
  have hGm2 : ∀ m, ∀ᵐ x ∂μ, ‖Gm m x‖ ≤ 2 * Θr x := fun m => by
    filter_upwards [hinvμ] with x hx
    exact (tflPsi_inv_le_two W b σ E z hX hz (hκpos m) x hx).trans (by linarith [hGΘ x])
  have hGmlim : ∀ᵐ x ∂μ, Tendsto (fun m => Gm m x) atTop (𝓝 (Gr x)) := by
    filter_upwards [hinvμ] with x hx
    exact tcv_G_tendsto σ E z hx hκlim
  have hl1 := dcv_cov_tendsto (μ := μ) (fm := fun m x => φ1 (Gm m x)) (f := fun x => φ1 (Gr x))
    (Um := Gm) (U := Gr) (fun m => ((hφ1c.comp (hGmc m))).aestronglyMeasurable)
    (fun m => (hGmc m).aestronglyMeasurable) (hi2.const_mul (16 * ‖P‖)) (hi1.const_mul 2)
    (hi3.const_mul (32 * ‖P‖))
    (fun m => by filter_upwards [hGm2 m] with x hx; exact (hdom _ _ hx).1)
    (fun m => by filter_upwards [hGm2 m] with x hx; exact (hdom _ _ hx).2.1)
    (fun m => by filter_upwards [hGm2 m] with x hx; exact (hdom _ _ hx).2.2.1)
    (by filter_upwards [hGmlim] with x hx; exact (hφ1c.tendsto _).comp hx) hGmlim
  have hl2 := dcv_cov_tendsto (μ := μ) (fm := fun m x => φ2 (Gm m x)) (f := fun x => φ2 (Gr x))
    (Um := fun m x => ψ2 (Gm m x)) (U := fun x => ψ2 (Gr x))
    (fun m => ((hφ2c.comp (hGmc m))).aestronglyMeasurable)
    (fun m => ((hψ2c.comp (hGmc m))).aestronglyMeasurable) (hi1.const_mul 8)
    (hi2.const_mul (4 * ‖P‖)) (hi3.const_mul (32 * ‖P‖))
    (fun m => by filter_upwards [hGm2 m] with x hx; exact (hdom _ _ hx).2.2.2.1)
    (fun m => by filter_upwards [hGm2 m] with x hx; exact (hdom _ _ hx).2.2.2.2.1)
    (fun m => by filter_upwards [hGm2 m] with x hx; exact (hdom _ _ hx).2.2.2.2.2)
    (by filter_upwards [hGmlim] with x hx; exact (hφ2c.tendsto _).comp hx)
    (by filter_upwards [hGmlim] with x hx; exact (hψ2c.tendsto _).comp hx)
  refine le_of_tendsto' (hl1.add hl2).norm fun m => ?_
  -- the bound at `κ_m`
  have hfix := dcv_cov_fixed σ E z hW hb0 hb1 hX hz hD P Kh hs hP (hκpos m)
  refine hfix.trans ?_
  have hc0 : 0 ≤ 80 * s / (W : ℝ) ^ 2 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hc0
  have hΘm : ∀ᵐ x ∂μ, dcvTheta Kh (tcvG W b σ E z X (κm m) x) ≤ 2 * Θr x := by
    filter_upwards [hinvμ] with x hx
    rw [tcvG, tflPsi_inv_eq]
    exact dcv_theta_reg_layer σ E hX _ (tflEmbed_blockDiag_isHermitian W b σ x) hz (hκpos m) hx Kh
  have hΘmi : Integrable (fun x => dcvTheta Kh (tcvG W b σ E z X (κm m) x) ^ 5) μ :=
    Integrable.mono' ((hint 5 (by norm_num) le_rfl).const_mul (2 ^ 5))
      (((dcv_continuous_theta Kh).comp (hGmc m)).pow 5).aestronglyMeasurable
      (by
        filter_upwards [hΘm] with x hx
        rw [Real.norm_of_nonneg (pow_nonneg (dcvTheta_nonneg _ _) _), ← mul_pow]
        exact pow_le_pow_left₀ (dcvTheta_nonneg _ _) hx 5)
  calc ∫ x, dcvTheta Kh (tcvG W b σ E z X (κm m) x) ^ 5 ∂μ ≤ ∫ x, 2 ^ 5 * Θr x ^ 5 ∂μ := by
        refine integral_mono_ae hΘmi ((hint 5 (by norm_num) le_rfl).const_mul _) ?_
        filter_upwards [hΘm] with x hx
        rw [← mul_pow]
        exact pow_le_pow_left₀ (dcvTheta_nonneg _ _) hx 5
    _ = 2 ^ 5 * ∫ x, Θr x ^ 5 ∂μ := integral_const_mul _ _
    _ ≤ 2 ^ 5 * CT ^ 5 := by gcongr
    _ = 32 * CT ^ 5 := by norm_num

end Core

/-!
## 4. The derivative of the covariance (Steps 1 and 3)
-/

section Derivative

/-- `a^i c^j ≤ 1 + a⁴ + c⁴` for `a, c ≥ 0`, `i + j ≤ 4`. -/
theorem dcv_mono_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) {i j : ℕ} (hij : i + j ≤ 4) :
    a ^ i * c ^ j ≤ 1 + a ^ 4 + c ^ 4 := by
  set m := max a c with hm
  have hm0 : 0 ≤ m := le_max_of_le_left ha
  have h1 : a ^ i * c ^ j ≤ m ^ (i + j) := by
    rw [pow_add]
    exact mul_le_mul (pow_le_pow_left₀ ha (le_max_left _ _) _)
      (pow_le_pow_left₀ hc (le_max_right _ _) _) (pow_nonneg hc _) (pow_nonneg hm0 _)
  have h2 : m ^ (i + j) ≤ 1 + m ^ 4 := by
    rcases le_total m 1 with h | h
    · have := pow_le_one₀ hm0 h (n := i + j)
      nlinarith [pow_nonneg hm0 4]
    · have := pow_le_pow_right₀ h hij
      linarith
  have h3 : m ^ 4 ≤ a ^ 4 + c ^ 4 := by
    rcases le_total a c with h | h
    · rw [hm, max_eq_right h]; linarith [pow_nonneg ha 4]
    · rw [hm, max_eq_left h]; linarith [pow_nonneg hc 4]
  linarith

/-- `HasDerivAt` from a quadratic remainder bound on `|t| ≤ 1`. -/
theorem dcv_hasDerivAt_of_sq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : ℝ → F}
    {φ' : F} {K : ℝ} (h : ∀ t : ℝ, |t| ≤ 1 → ‖φ t - φ 0 - t • φ'‖ ≤ K * t ^ 2) :
    HasDerivAt φ φ' 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun t : ℝ => φ (0 + t) - φ 0 - t • φ') =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine IsBigO.of_bound K ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    rw [zero_add, Real.norm_of_nonneg (sq_nonneg t)]
    exact h t ht.le
  exact hO.trans_isLittleO (isLittleO_pow_id (by norm_num))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Second-order resolvent expansion** (deterministic): if `G_h - G₀ = -h G_h P G₀`, then with
`𝒢̇ = -G₀ P G₀`, `Q = 1 + ‖G_h‖⁴ + ‖G₀‖⁴` and `‖τ N‖ ≤ c_τ ‖N‖`:
`‖G_h - G₀‖ ≤ |h| ‖P‖ Q`, `‖G_h - G₀ - h𝒢̇‖ ≤ h² ‖P‖² Q`, the same for `τ` with `c_τ`, and
`‖τ(G_h) G_h - τ(G₀) G₀ - h(τ(𝒢̇) G₀ + τ(G₀) 𝒢̇)‖ ≤ 3 c_τ ‖P‖² h² Q`. -/
theorem dcv_expand_le (τ : Matrix ι ι ℂ →L[ℝ] ℂ) {cτ : ℝ} (hcτ : 0 ≤ cτ)
    (hτ : ∀ N, ‖τ N‖ ≤ cτ * ‖N‖) {Gh G0 P : Matrix ι ι ℂ} {h : ℝ}
    (hres : Gh - G0 = -((h : ℂ) • (Gh * P * G0))) :
    ‖Gh - G0‖ ≤ |h| * (‖P‖ * (1 + ‖Gh‖ ^ 4 + ‖G0‖ ^ 4)) ∧
    ‖Gh - G0 - (h : ℂ) • -(G0 * P * G0)‖ ≤ h ^ 2 * (‖P‖ ^ 2 * (1 + ‖Gh‖ ^ 4 + ‖G0‖ ^ 4)) ∧
    ‖τ Gh - τ G0 - (h : ℂ) * τ (-(G0 * P * G0))‖ ≤
      h ^ 2 * (cτ * ‖P‖ ^ 2 * (1 + ‖Gh‖ ^ 4 + ‖G0‖ ^ 4)) ∧
    ‖τ Gh • Gh - τ G0 • G0 - (h : ℂ) • (τ (-(G0 * P * G0)) • G0 + τ G0 • -(G0 * P * G0))‖ ≤
      h ^ 2 * (3 * cτ * ‖P‖ ^ 2 * (1 + ‖Gh‖ ^ 4 + ‖G0‖ ^ 4)) := by
  set a := ‖Gh‖ with ha
  set c := ‖G0‖ with hc
  set p := ‖P‖ with hp
  set Q := 1 + a ^ 4 + c ^ 4 with hQ
  set Gd := -(G0 * P * G0) with hGd
  have ha0 : 0 ≤ a := norm_nonneg _
  have hc0 : 0 ≤ c := norm_nonneg _
  have hp0 : 0 ≤ p := norm_nonneg _
  have hh0 : 0 ≤ |h| := abs_nonneg h
  have hhc : ‖(h : ℂ)‖ = |h| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hh2 : |h| ^ 2 = h ^ 2 := sq_abs h
  have m3 : ∀ A B C : Matrix ι ι ℂ, ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := fun A B C =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  -- (1) first order
  have e1 : ‖Gh - G0‖ ≤ |h| * (p * (a * c)) := by
    rw [hres, norm_neg, norm_smul, hhc]
    refine mul_le_mul_of_nonneg_left ((m3 _ _ _).trans (le_of_eq ?_)) hh0
    ring
  have q11 : a * c ≤ Q := by simpa using dcv_mono_le ha0 hc0 (i := 1) (j := 1) (by norm_num)
  have q12 : a * c ^ 2 ≤ Q := by simpa using dcv_mono_le ha0 hc0 (i := 1) (j := 2) (by norm_num)
  have q22 : a ^ 2 * c ^ 2 ≤ Q := dcv_mono_le ha0 hc0 (by norm_num)
  have q13 : a * c ^ 3 ≤ Q := by simpa using dcv_mono_le ha0 hc0 (i := 1) (j := 3) (by norm_num)
  -- (2) second order
  have e2eq : Gh - G0 - (h : ℂ) • Gd = ((h : ℂ) ^ 2) • (Gh * P * G0 * P * G0) := by
    have h1 : (Gh - G0) * P * G0 = -((h : ℂ) • (Gh * P * G0 * P * G0)) := by
      rw [hres, Matrix.neg_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.smul_mul]
    have h2 : Gh - G0 - (h : ℂ) • Gd = -((h : ℂ) • ((Gh - G0) * P * G0)) := by
      rw [Matrix.sub_mul, Matrix.sub_mul, hGd]
      conv_lhs => rw [hres]
      module
    rw [h2, h1]
    module
  have e2 : ‖Gh - G0 - (h : ℂ) • Gd‖ ≤ h ^ 2 * (p ^ 2 * (a * c ^ 2)) := by
    rw [e2eq, norm_smul, norm_pow, hhc, hh2]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg h)
    have : ‖Gh * P * G0 * P * G0‖ ≤ a * p * c * p * c := by
      refine (norm_mul_le _ _).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hc0
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (m3 _ _ _) hp0
    exact this.trans (le_of_eq (by ring))
  -- (3) the trace
  have hτs : ∀ N : Matrix ι ι ℂ, τ ((h : ℂ) • N) = (h : ℂ) * τ N := fun N => by
    rw [Complex.coe_smul, map_smul, Complex.real_smul]
  have e3eq : τ Gh - τ G0 - (h : ℂ) * τ Gd = τ (Gh - G0 - (h : ℂ) • Gd) := by
    rw [map_sub, map_sub, hτs]
  have e3 : ‖τ Gh - τ G0 - (h : ℂ) * τ Gd‖ ≤ cτ * (h ^ 2 * (p ^ 2 * (a * c ^ 2))) := by
    rw [e3eq]; exact (hτ _).trans (mul_le_mul_of_nonneg_left e2 hcτ)
  -- (4) the product
  have e4eq : τ Gh • Gh - τ G0 • G0 - (h : ℂ) • (τ Gd • G0 + τ G0 • Gd) =
      (τ Gh - τ G0 - (h : ℂ) * τ Gd) • Gh + τ G0 • (Gh - G0 - (h : ℂ) • Gd) +
        ((h : ℂ) * τ Gd) • (Gh - G0) := by module
  have hGdn : ‖Gd‖ ≤ p * c ^ 2 := by
    rw [hGd, norm_neg]; exact (m3 _ _ _).trans (le_of_eq (by ring))
  have hτGd : ‖τ Gd‖ ≤ cτ * (p * c ^ 2) := (hτ _).trans (mul_le_mul_of_nonneg_left hGdn hcτ)
  have hτG0 : ‖τ G0‖ ≤ cτ * c := hτ _
  have e4 : ‖τ Gh • Gh - τ G0 • G0 - (h : ℂ) • (τ Gd • G0 + τ G0 • Gd)‖ ≤
      h ^ 2 * (3 * cτ * p ^ 2 * Q) := by
    rw [e4eq]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_smul, norm_smul, norm_smul, norm_mul, hhc]
    have t1 : ‖τ Gh - τ G0 - (h : ℂ) * τ Gd‖ * a ≤ cτ * (h ^ 2 * (p ^ 2 * (a * c ^ 2))) * a :=
      mul_le_mul_of_nonneg_right e3 ha0
    have t2 : ‖τ G0‖ * ‖Gh - G0 - (h : ℂ) • Gd‖ ≤ (cτ * c) * (h ^ 2 * (p ^ 2 * (a * c ^ 2))) :=
      mul_le_mul hτG0 e2 (norm_nonneg _) (by positivity)
    have t3 : |h| * ‖τ Gd‖ * ‖Gh - G0‖ ≤ |h| * (cτ * (p * c ^ 2)) * (|h| * (p * (a * c))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hτGd hh0) e1 (norm_nonneg _) (by positivity)
    have hk : 0 ≤ cτ * p ^ 2 * h ^ 2 := by positivity
    have s1 : cτ * (h ^ 2 * (p ^ 2 * (a * c ^ 2))) * a = cτ * p ^ 2 * h ^ 2 * (a ^ 2 * c ^ 2) := by
      ring
    have s2 : (cτ * c) * (h ^ 2 * (p ^ 2 * (a * c ^ 2))) = cτ * p ^ 2 * h ^ 2 * (a * c ^ 3) := by
      ring
    have s3 : |h| * (cτ * (p * c ^ 2)) * (|h| * (p * (a * c))) =
        cτ * p ^ 2 * h ^ 2 * (a * c ^ 3) := by
      rw [← hh2]; ring
    have u1 := mul_le_mul_of_nonneg_left q22 hk
    have u2 := mul_le_mul_of_nonneg_left q13 hk
    nlinarith
  refine ⟨e1.trans ?_, e2.trans ?_, e3.trans ?_, e4⟩
  · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left q11 hp0) hh0
  · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left q12 (by positivity)) (sq_nonneg h)
  · have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left q12 (sq_nonneg p))
      (sq_nonneg h)
    calc cτ * (h ^ 2 * (p ^ 2 * (a * c ^ 2))) ≤ cτ * (h ^ 2 * (p ^ 2 * Q)) :=
          mul_le_mul_of_nonneg_left this hcτ
      _ = h ^ 2 * (cτ * p ^ 2 * Q) := by ring

/-- The entry functional `N ↦ N x y`. -/
def dcvEntry (x y : ι) : Matrix ι ι ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun N => N x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Entrywise expectation is the Bochner integral for integrable matrices. -/
theorem dcv_matrixExpect_eq_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : Ω → Matrix ι ι ℂ} (hU : Integrable U μ) : matrixExpect μ U = ∫ ω, U ω ∂μ := by
  ext x y
  simp only [matrixExpect, of_apply]
  exact (dcvEntry x y).integral_comp_comm hU

/-- The algebra of the quadratic remainder of `t ↦ F(t) - m(t) M(t)`. -/
theorem dcv_quad_alg {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] (t : ℝ)
    (Ft F0 F1 F2 Mt M0 M' : M) (mt m0 m' : ℂ) {A1 A2 A3 A4 B1 B2 B3 : ℝ} (hB2 : 0 ≤ B2)
    (h1 : ‖Ft - F0 - (t : ℂ) • (F1 + F2)‖ ≤ A1 * t ^ 2)
    (h2 : ‖mt - m0 - (t : ℂ) * m'‖ ≤ A2 * t ^ 2) (h3 : ‖Mt‖ ≤ B1) (h4 : ‖m0‖ ≤ B2)
    (h5 : ‖Mt - M0 - (t : ℂ) • M'‖ ≤ A3 * t ^ 2) (h6 : ‖m'‖ ≤ B3) (h7 : ‖Mt - M0‖ ≤ A4 * |t|) :
    ‖(Ft - mt • Mt) - (F0 - m0 • M0) - t • ((F1 - m' • M0) + (F2 - m0 • M'))‖ ≤
      (A1 + A2 * B1 + B2 * A3 + B3 * A4) * t ^ 2 := by
  rw [← Complex.coe_smul]
  have e : (Ft - mt • Mt) - (F0 - m0 • M0) - (t : ℂ) • ((F1 - m' • M0) + (F2 - m0 • M')) =
      (Ft - F0 - (t : ℂ) • (F1 + F2)) - ((mt - m0 - (t : ℂ) * m') • Mt +
        m0 • (Mt - M0 - (t : ℂ) • M') + ((t : ℂ) * m') • (Mt - M0)) := by module
  rw [e]
  have hA2 : 0 ≤ A2 * t ^ 2 := (norm_nonneg _).trans h2
  have hB3 : 0 ≤ B3 := (norm_nonneg _).trans h6
  have hA4 : 0 ≤ A4 * |t| := (norm_nonneg _).trans h7
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add le_rfl ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))).trans ?_
  rw [norm_smul, norm_smul, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have t1 : ‖mt - m0 - (t : ℂ) * m'‖ * ‖Mt‖ ≤ A2 * t ^ 2 * B1 :=
    mul_le_mul h2 h3 (norm_nonneg _) hA2
  have t2 : ‖m0‖ * ‖Mt - M0 - (t : ℂ) • M'‖ ≤ B2 * (A3 * t ^ 2) :=
    mul_le_mul h4 h5 (norm_nonneg _) hB2
  have t3 : |t| * ‖m'‖ * ‖Mt - M0‖ ≤ |t| * B3 * (A4 * |t|) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h6 (abs_nonneg t)) h7 (norm_nonneg _)
      (mul_nonneg (abs_nonneg t) hB3)
  have s3 : |t| * B3 * (A4 * |t|) = B3 * A4 * t ^ 2 := by rw [← sq_abs t]; ring
  nlinarith

/-- `‖∫ f‖ ≤ k ∫ g` from `‖f‖ ≤ k g` a.e. -/
theorem dcv_norm_integral_le {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Ω → E} {g : Ω → ℝ} (hg : Integrable g μ)
    {k : ℝ} (hfg : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ k * g ω) : ‖∫ ω, f ω ∂μ‖ ≤ k * ∫ ω, g ω ∂μ :=
  (norm_integral_le_of_norm_le (hg.const_mul k) hfg).trans (le_of_eq (integral_const_mul _ _))

/-- **Derivative of the covariance** (abstract form of Steps 1 and 3): for a family `G_h` with
the resolvent identity `G_h - G₀ = -h G_h P G₀` a.e. and `E‖G_h‖⁴ ≤ C₄` for `|h| ≤ 1`, and an
`ℝ`-linear `τ` with `‖τ N‖ ≤ c_τ ‖N‖`, `h ↦ Cov(τ(G_h), G_h)` is differentiable at `0` with
derivative `Cov(τ(𝒢̇), G₀) + Cov(τ(G₀), 𝒢̇)`, `𝒢̇ = -G₀ P G₀`. -/
theorem dcv_hasDerivAt_cov {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (G : ℝ → Ω → Matrix ι ι ℂ) (P : Matrix ι ι ℂ)
    (τ : Matrix ι ι ℂ →L[ℝ] ℂ) {cτ : ℝ} (hcτ : 0 ≤ cτ) (hτ : ∀ N, ‖τ N‖ ≤ cτ * ‖N‖)
    (hGm : ∀ h, Measurable (G h))
    (hres : ∀ h : ℝ, ∀ᵐ ω ∂μ, G h ω - G 0 ω = -((h : ℂ) • (G h ω * P * G 0 ω)))
    {C4 : ℝ} (hmom : ∀ h : ℝ, |h| ≤ 1 →
      Integrable (fun ω => ‖G h ω‖ ^ 4) μ ∧ ∫ ω, ‖G h ω‖ ^ 4 ∂μ ≤ C4) :
    HasDerivAt (fun h : ℝ => dcvCov μ (fun ω => τ (G h ω)) (G h))
      (dcvCov μ (fun ω => τ (-(G 0 ω * P * G 0 ω))) (G 0) +
        dcvCov μ (fun ω => τ (G 0 ω)) (fun ω => -(G 0 ω * P * G 0 ω))) 0 := by
  set p := ‖P‖ with hp
  have hp0 : 0 ≤ p := norm_nonneg _
  set Gd : Ω → Matrix ι ι ℂ := fun ω => -(G 0 ω * P * G 0 ω) with hGd
  have h0 : |(0 : ℝ)| ≤ 1 := by simp
  have hC4 : 0 ≤ C4 := (integral_nonneg fun ω => by positivity).trans (hmom 0 h0).2
  set Q : ℝ → Ω → ℝ := fun h ω => 1 + ‖G h ω‖ ^ 4 + ‖G 0 ω‖ ^ 4 with hQ
  set B := 1 + 2 * C4 with hB
  have hB0 : 0 ≤ B := by positivity
  have hQi : ∀ h, |h| ≤ 1 → Integrable (Q h) μ := fun h hh =>
    ((integrable_const 1).add (hmom h hh).1).add (hmom 0 h0).1
  have hQB : ∀ h, |h| ≤ 1 → ∫ ω, Q h ω ∂μ ≤ B := fun h hh => by
    simp only [hQ]
    have i1 : Integrable (fun ω => (1 : ℝ) + ‖G h ω‖ ^ 4) μ :=
      (integrable_const 1).add (hmom h hh).1
    rw [integral_add i1 (hmom 0 h0).1, integral_add (integrable_const 1) (hmom h hh).1,
      integral_const, probReal_univ, one_smul]
    linarith [(hmom h hh).2, (hmom 0 h0).2]
  have mono : ∀ h ω (i j : ℕ), i + j ≤ 4 → ‖G h ω‖ ^ i * ‖G 0 ω‖ ^ j ≤ Q h ω :=
    fun h ω i j hij => dcv_mono_le (norm_nonneg _) (norm_nonneg _) hij
  have hGQ : ∀ h ω, ‖G h ω‖ ≤ Q h ω := fun h ω => by simpa using mono h ω 1 0 (by norm_num)
  have hG0Q : ∀ h ω, ‖G 0 ω‖ ≤ Q h ω := fun h ω => by simpa using mono h ω 0 1 (by norm_num)
  have hGG : ∀ h ω, ‖G h ω‖ * ‖G h ω‖ ≤ Q h ω := fun h ω => by
    simpa [sq] using mono h ω 2 0 (by norm_num)
  have hG02 : ∀ ω, ‖G 0 ω‖ ^ 2 ≤ Q 0 ω := fun ω => by simpa using mono 0 ω 0 2 (by norm_num)
  have hG03 : ∀ ω, ‖G 0 ω‖ ^ 3 ≤ Q 0 ω := fun ω => by simpa using mono 0 ω 0 3 (by norm_num)
  have m3 : ∀ A B C : Matrix ι ι ℂ, ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := fun A B C =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have hGdn : ∀ ω, ‖Gd ω‖ ≤ p * ‖G 0 ω‖ ^ 2 := fun ω => by
    simp only [hGd, norm_neg]; exact (m3 _ _ _).trans (le_of_eq (by ring))
  -- measurability
  have hτc : Continuous τ := τ.continuous
  have mG : ∀ h, AEStronglyMeasurable (G h) μ := fun h => (hGm h).aestronglyMeasurable
  have mg : ∀ h, AEStronglyMeasurable (fun ω => τ (G h ω)) μ := fun h =>
    (hτc.measurable.comp (hGm h)).aestronglyMeasurable
  have hGdm : Measurable Gd :=
    (((continuous_id.mul continuous_const).mul continuous_id).neg.measurable).comp (hGm 0)
  have mGd : AEStronglyMeasurable Gd μ := hGdm.aestronglyMeasurable
  have mgd : AEStronglyMeasurable (fun ω => τ (Gd ω)) μ :=
    (hτc.measurable.comp hGdm).aestronglyMeasurable
  -- integrability
  have iG : ∀ h, |h| ≤ 1 → Integrable (G h) μ := fun h hh =>
    Integrable.mono' (hQi h hh) (mG h) (ae_of_all _ fun ω => hGQ h ω)
  have ig : ∀ h, |h| ≤ 1 → Integrable (fun ω => τ (G h ω)) μ := fun h hh =>
    Integrable.mono' ((hQi h hh).const_mul cτ) (mg h) (ae_of_all _ fun ω =>
      (hτ _).trans (mul_le_mul_of_nonneg_left (hGQ h ω) hcτ))
  have igG : ∀ h, |h| ≤ 1 → Integrable (fun ω => τ (G h ω) • G h ω) μ := fun h hh =>
    Integrable.mono' ((hQi h hh).const_mul cτ) ((mg h).smul (mG h)) (ae_of_all _ fun ω => by
      rw [norm_smul]
      calc ‖τ (G h ω)‖ * ‖G h ω‖ ≤ (cτ * ‖G h ω‖) * ‖G h ω‖ :=
            mul_le_mul_of_nonneg_right (hτ _) (norm_nonneg _)
        _ = cτ * (‖G h ω‖ * ‖G h ω‖) := by ring
        _ ≤ cτ * Q h ω := mul_le_mul_of_nonneg_left (hGG h ω) hcτ)
  have iGd : Integrable Gd μ :=
    Integrable.mono' ((hQi 0 h0).const_mul p) mGd (ae_of_all _ fun ω =>
      (hGdn ω).trans (mul_le_mul_of_nonneg_left (hG02 ω) hp0))
  have igd : Integrable (fun ω => τ (Gd ω)) μ :=
    Integrable.mono' ((hQi 0 h0).const_mul (cτ * p)) mgd (ae_of_all _ fun ω =>
      (hτ _).trans (by
        calc cτ * ‖Gd ω‖ ≤ cτ * (p * ‖G 0 ω‖ ^ 2) := mul_le_mul_of_nonneg_left (hGdn ω) hcτ
          _ ≤ cτ * (p * Q 0 ω) := by gcongr; exact hG02 ω
          _ = cτ * p * Q 0 ω := by ring))
  have igdG : Integrable (fun ω => τ (Gd ω) • G 0 ω) μ :=
    Integrable.mono' ((hQi 0 h0).const_mul (cτ * p)) (mgd.smul (mG 0)) (ae_of_all _ fun ω => by
      rw [norm_smul]
      calc ‖τ (Gd ω)‖ * ‖G 0 ω‖ ≤ (cτ * (p * ‖G 0 ω‖ ^ 2)) * ‖G 0 ω‖ :=
            mul_le_mul_of_nonneg_right ((hτ _).trans (mul_le_mul_of_nonneg_left (hGdn ω) hcτ))
              (norm_nonneg _)
        _ = cτ * p * ‖G 0 ω‖ ^ 3 := by ring
        _ ≤ cτ * p * Q 0 ω := mul_le_mul_of_nonneg_left (hG03 ω) (by positivity))
  have igGd : Integrable (fun ω => τ (G 0 ω) • Gd ω) μ :=
    Integrable.mono' ((hQi 0 h0).const_mul (cτ * p)) ((mg 0).smul mGd) (ae_of_all _ fun ω => by
      rw [norm_smul]
      calc ‖τ (G 0 ω)‖ * ‖Gd ω‖ ≤ (cτ * ‖G 0 ω‖) * (p * ‖G 0 ω‖ ^ 2) :=
            mul_le_mul (hτ _) (hGdn ω) (norm_nonneg _) (by positivity)
        _ = cτ * p * ‖G 0 ω‖ ^ 3 := by ring
        _ ≤ cτ * p * Q 0 ω := mul_le_mul_of_nonneg_left (hG03 ω) (by positivity))
  -- the Bochner form
  set φ : ℝ → Matrix ι ι ℂ := fun h =>
    (∫ ω, τ (G h ω) • G h ω ∂μ) - (∫ ω, τ (G h ω) ∂μ) • ∫ ω, G h ω ∂μ with hφ
  have hcov : ∀ h, |h| ≤ 1 → dcvCov μ (fun ω => τ (G h ω)) (G h) = φ h := fun h hh => by
    simp only [dcvCov, hφ]
    rw [dcv_matrixExpect_eq_integral (igG h hh), dcv_matrixExpect_eq_integral (iG h hh)]
  have hder : dcvCov μ (fun ω => τ (Gd ω)) (G 0) + dcvCov μ (fun ω => τ (G 0 ω)) Gd =
      ((∫ ω, τ (Gd ω) • G 0 ω ∂μ) - (∫ ω, τ (Gd ω) ∂μ) • ∫ ω, G 0 ω ∂μ) +
        ((∫ ω, τ (G 0 ω) • Gd ω ∂μ) - (∫ ω, τ (G 0 ω) ∂μ) • ∫ ω, Gd ω ∂μ) := by
    simp only [dcvCov]
    rw [dcv_matrixExpect_eq_integral igdG, dcv_matrixExpect_eq_integral (iG 0 h0),
      dcv_matrixExpect_eq_integral igGd, dcv_matrixExpect_eq_integral iGd]
  rw [hder]
  have hev : (fun h : ℝ => dcvCov μ (fun ω => τ (G h ω)) (G h)) =ᶠ[𝓝 0] φ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    exact hcov t ht.le
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  refine dcv_hasDerivAt_of_sq (K := 3 * cτ * p ^ 2 * B + cτ * p ^ 2 * B * B + cτ * B * (p ^ 2 * B) +
    cτ * p * B * (p * B)) fun t ht => ?_
  -- pointwise expansions
  have hexp : ∀ᵐ ω ∂μ, _ := (hres t).mono fun ω hω =>
    dcv_expand_le τ hcτ hτ (Gh := G t ω) (G0 := G 0 ω) (P := P) hω
  -- the seven integral bounds
  have b1 : ‖(∫ ω, τ (G t ω) • G t ω ∂μ) - (∫ ω, τ (G 0 ω) • G 0 ω ∂μ) -
      (t : ℂ) • ((∫ ω, τ (Gd ω) • G 0 ω ∂μ) + ∫ ω, τ (G 0 ω) • Gd ω ∂μ)‖ ≤
      3 * cτ * p ^ 2 * B * t ^ 2 := by
    have j1 : Integrable (fun ω => τ (G t ω) • G t ω - τ (G 0 ω) • G 0 ω) μ :=
      (igG t ht).sub (igG 0 h0)
    have j2 : Integrable (fun ω => (t : ℂ) • (τ (Gd ω) • G 0 ω + τ (G 0 ω) • Gd ω)) μ :=
      (igdG.add igGd).smul (t : ℂ)
    rw [← integral_add igdG igGd, ← integral_smul, ← integral_sub (igG t ht) (igG 0 h0),
      ← integral_sub j1 j2]
    refine (dcv_norm_integral_le (hQi t ht) (k := t ^ 2 * (3 * cτ * p ^ 2)) ?_).trans ?_
    · filter_upwards [hexp] with ω hω
      have := hω.2.2.2
      simp only [hGd] at this ⊢
      refine this.trans (le_of_eq ?_)
      simp only [hQ]; ring
    · have := mul_le_mul_of_nonneg_left (hQB t ht) (by positivity : 0 ≤ t ^ 2 * (3 * cτ * p ^ 2))
      linarith
  have b2 : ‖(∫ ω, τ (G t ω) ∂μ) - (∫ ω, τ (G 0 ω) ∂μ) - (t : ℂ) * ∫ ω, τ (Gd ω) ∂μ‖ ≤
      cτ * p ^ 2 * B * t ^ 2 := by
    have j1 : Integrable (fun ω => τ (G t ω) - τ (G 0 ω)) μ := (ig t ht).sub (ig 0 h0)
    have j2 : Integrable (fun ω => (t : ℂ) * τ (Gd ω)) μ := igd.const_mul _
    rw [← integral_const_mul, ← integral_sub (ig t ht) (ig 0 h0), ← integral_sub j1 j2]
    refine (dcv_norm_integral_le (hQi t ht) (k := t ^ 2 * (cτ * p ^ 2)) ?_).trans ?_
    · filter_upwards [hexp] with ω hω
      have := hω.2.2.1
      simp only [hGd] at this ⊢
      refine this.trans (le_of_eq ?_)
      simp only [hQ]; ring
    · have := mul_le_mul_of_nonneg_left (hQB t ht) (by positivity : 0 ≤ t ^ 2 * (cτ * p ^ 2))
      linarith
  have b3 : ‖∫ ω, G t ω ∂μ‖ ≤ B := by
    refine (dcv_norm_integral_le (hQi t ht) (k := 1) (ae_of_all _ fun ω => ?_)).trans ?_
    · rw [one_mul]; exact hGQ t ω
    · rw [one_mul]; exact hQB t ht
  have b4 : ‖∫ ω, τ (G 0 ω) ∂μ‖ ≤ cτ * B := by
    refine (dcv_norm_integral_le (hQi 0 h0) (k := cτ) (ae_of_all _ fun ω => ?_)).trans ?_
    · exact (hτ _).trans (mul_le_mul_of_nonneg_left (hGQ 0 ω) hcτ)
    · exact mul_le_mul_of_nonneg_left (hQB 0 h0) hcτ
  have b5 : ‖(∫ ω, G t ω ∂μ) - (∫ ω, G 0 ω ∂μ) - (t : ℂ) • ∫ ω, Gd ω ∂μ‖ ≤ p ^ 2 * B * t ^ 2 := by
    have j1 : Integrable (fun ω => G t ω - G 0 ω) μ := (iG t ht).sub (iG 0 h0)
    have j2 : Integrable (fun ω => (t : ℂ) • Gd ω) μ := iGd.smul (t : ℂ)
    rw [← integral_smul, ← integral_sub (iG t ht) (iG 0 h0), ← integral_sub j1 j2]
    refine (dcv_norm_integral_le (hQi t ht) (k := t ^ 2 * p ^ 2) ?_).trans ?_
    · filter_upwards [hexp] with ω hω
      have := hω.2.1
      simp only [hGd] at this ⊢
      refine this.trans (le_of_eq ?_)
      simp only [hQ]; ring
    · have := mul_le_mul_of_nonneg_left (hQB t ht) (by positivity : 0 ≤ t ^ 2 * p ^ 2)
      linarith
  have b6 : ‖∫ ω, τ (Gd ω) ∂μ‖ ≤ cτ * p * B := by
    refine (dcv_norm_integral_le (hQi 0 h0) (k := cτ * p) (ae_of_all _ fun ω => ?_)).trans ?_
    · calc ‖τ (Gd ω)‖ ≤ cτ * (p * ‖G 0 ω‖ ^ 2) :=
            (hτ _).trans (mul_le_mul_of_nonneg_left (hGdn ω) hcτ)
        _ ≤ cτ * (p * Q 0 ω) := by gcongr; exact hG02 ω
        _ = cτ * p * Q 0 ω := by ring
    · exact mul_le_mul_of_nonneg_left (hQB 0 h0) (by positivity)
  have b7 : ‖(∫ ω, G t ω ∂μ) - ∫ ω, G 0 ω ∂μ‖ ≤ p * B * |t| := by
    rw [← integral_sub (iG t ht) (iG 0 h0)]
    refine (dcv_norm_integral_le (hQi t ht) (k := |t| * p) ?_).trans ?_
    · filter_upwards [hexp] with ω hω
      refine hω.1.trans (le_of_eq ?_)
      simp only [hQ]; ring
    · have := mul_le_mul_of_nonneg_left (hQB t ht) (by positivity : 0 ≤ |t| * p)
      linarith
  have hfin := dcv_quad_alg t _ _ _ _ _ _ _ _ _ _ (by positivity : (0 : ℝ) ≤ cτ * B) b1 b2 b3 b4
    b5 b6 b7
  refine hfin.trans (le_of_eq ?_)
  ring

/-- **`∂_h Cov(g_i, 𝒢)` at `h = 0`** for the source family `X(h) = X - hS` (Steps 1 and 3):
with a.e. invertibility at every `X - hS` and `E‖𝒢(h)‖⁴ ≤ C₄` for `|h| ≤ 1`, the map
`h ↦ Cov(W⁻¹ Tr(D 𝒢(h)), 𝒢(h))` has derivative `dcvCovDir μ D 𝒢 Ŝ` at `0`. -/
theorem dcv_hasDerivAt_cov_layer {W : ℕ} (hW : 0 < W) {b : ℝ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X S : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (hinv : ∀ h : ℝ, ∀ᵐ ω ∂layerLaw W b σ,
      IsUnit (layerMatrix σ E z (X - (h : ℂ) • S) ω).det)
    {C4 : ℝ} (hmom : ∀ h : ℝ, |h| ≤ 1 →
      Integrable (fun ω => ‖layerResolvent σ E z (X - (h : ℂ) • S) ω‖ ^ 4) (layerLaw W b σ) ∧
        ∫ ω, ‖layerResolvent σ E z (X - (h : ℂ) • S) ω‖ ^ 4 ∂layerLaw W b σ ≤ C4) :
    HasDerivAt (fun h : ℝ => dcvCov (layerLaw W b σ)
        (fun ω => (W : ℂ)⁻¹ * (D * layerResolvent σ E z (X - (h : ℂ) • S) ω).trace)
        (fun ω => layerResolvent σ E z (X - (h : ℂ) • S) ω))
      (dcvCovDir (layerLaw W b σ) D (fun ω => layerResolvent σ E z X ω) (dcvHat S)) 0 := by
  have := bond_isProbabilityMeasure_layerLaw W b σ
  set P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ := dcvHat S with hPdef
  have hres : ∀ h : ℝ, ∀ᵐ ω ∂layerLaw W b σ,
      layerResolvent σ E z (X - (h : ℂ) • S) ω - layerResolvent σ E z (X - ((0 : ℝ) : ℂ) • S) ω =
        -((h : ℂ) • (layerResolvent σ E z (X - (h : ℂ) • S) ω * P *
          layerResolvent σ E z (X - ((0 : ℝ) : ℂ) • S) ω)) := fun h => by
    filter_upwards [hinv h, hinv 0] with ω h1 h0
    set Nh := layerMatrix σ E z (X - (h : ℂ) • S) ω with hNh
    set N0 := layerMatrix σ E z (X - ((0 : ℝ) : ℂ) • S) ω with hN0
    have k1 : Nh⁻¹ * Nh = 1 := nonsing_inv_mul _ h1
    have k0 : N0 * N0⁻¹ = 1 := mul_nonsing_inv _ h0
    have hdiff : N0 - Nh = -((h : ℂ) • P) := by
      rw [hNh, hN0, dcv_layerMatrix_sub, dcv_layerMatrix_sub]
      simp [hPdef]
    change Nh⁻¹ - N0⁻¹ = -((h : ℂ) • (Nh⁻¹ * P * N0⁻¹))
    calc Nh⁻¹ - N0⁻¹ = Nh⁻¹ * (N0 * N0⁻¹) - (Nh⁻¹ * Nh) * N0⁻¹ := by
          rw [k0, k1, Matrix.mul_one, Matrix.one_mul]
      _ = Nh⁻¹ * (N0 - Nh) * N0⁻¹ := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = -((h : ℂ) • (Nh⁻¹ * P * N0⁻¹)) := by
          rw [hdiff, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hd := dcv_hasDerivAt_cov (μ := layerLaw W b σ)
    (fun (h : ℝ) ω => layerResolvent σ E z (X - (h : ℂ) • S) ω) P (tflTraceCLM W σ D)
    (by positivity : (0 : ℝ) ≤ 4 * ‖D‖) (fun N => dcv_traceCLM_le σ hW D N)
    (fun h => measurable_layerResolvent σ E z _) hres hmom
  have hX0 : X - ((0 : ℝ) : ℂ) • S = X := by simp
  simp only [hX0] at hd
  convert hd using 1
  · rfl
  · unfold dcvCovDir
    simp only [map_neg, tflTraceCLM_apply]

end Derivative

/-!
## 5. The statement and its proof
-/

/-- **The differentiated-covariance lemma.**

*Setting and law.* "Condition on the old two-port path and its positive source `S`, before
exposing the next Gaussian layer": the conditioning data are deterministic, a Hermitian two-port
`X` (`2W × 2W`, the old Schur input) and `S ⪰ 0`; expectations, covariances and `L^p` norms are
over the fresh separate-port layer only, `μ = layerLaw W b .separate` (`A_a ~ GUE_W(c/W)`,
`c = 1 - 2b`, bonds `Gin(b/W)`), at `z = z_∂(E)`, `E ∈ bulkInterval κ` (every compact
`I ⋐ (-2,2)` lies in one). `K = z - X`, `Y = K⁻* S K⁻¹`, `u = W⁻¹ Re Tr Y`,
`Ŝ = dcvHat S = diag(S, 0)` (the old-input, i.e. physical, block of the augmented layer matrix
`𝒢⁻¹ = [[A - E - X, B], [B*, z]]`). The source family is exactly linear, `X(h) = X - hS` (no
`O(h²)` term), with `E`, `z` and every fresh coordinate fixed:
`𝒢(h) = layerResolvent .separate E z (X - hS)`, so `∂_h 𝒢(h)⁻¹ = Ŝ`. The normalized block trace
`g_i = W⁻¹ Tr P_i 𝒢` is stated for every deterministic `D` with `‖D‖ ≤ 1`
(`g = W⁻¹ Tr(D 𝒢)`; each block projection `P_i` of a physical block or a port has norm `≤ 1`),
a mild strengthening.

*Norms.* `‖·‖` is the `ℓ²` operator norm; `‖Y‖_HS = √(Re Tr Y²)`; covariances are entrywise
(`dcvCov`), `Cov(g, U) = E(gU) - (Eg)(EU)`; `L^p` norms are `eLpNorm` under `μ`.

*Clauses* (quantifiers: `b ∈ (0, 1/2)` and `κ > 0` first; then the insertion bound `K₀` and,
for the noise, the fixed moment order `p ≥ 1`; then `C` (resp. `C_p`) and `W₀`; then uniformly
in `W ≥ W₀`, Hermitian `X`, `S ⪰ 0` — "the constants are uniform in the old Hermitian
deformation and source" —, `E ∈ bulkInterval κ`, `‖D‖ ≤ 1` and `‖D₀‖ ≤ K₀`):
1. (the covariance derivative formula) `h ↦ Cov(g(h), 𝒢(h))` is differentiable at `h = 0` with
   derivative `dcvCovDir μ D 𝒢 Ŝ = Cov(ġ, 𝒢) + Cov(g, 𝒢̇)` (`𝒢̇ = -𝒢Ŝ𝒢`,
   `ġ = -W⁻¹ Tr(D 𝒢 Ŝ 𝒢)`), and `‖∂_h Cov(g, 𝒢)‖ ≤ C W⁻² ‖Y‖ ≤ C u / W`.
2. (the derivative-noise bound) `ġ` is the pointwise derivative of `h ↦ g(h)` at `0` (a.s.), and
   `‖ġ - Eġ‖_p ≤ C_p W^{-3/2} ‖Y‖_HS ≤ C_p u / √W`.
3. ("the corresponding assertions with a bounded deterministic insertion added to `Ŝ` have
   `1 + u` in place of `u`") with `Ŝ + D₀` in place of `Ŝ` in the derivative expressions
   (`dcvCovDir` and `ġ` are linear in the direction): `‖dcvCovDir μ D 𝒢 (Ŝ + D₀)‖ ≤ C(1+u)/W`
   and `‖ġ_{Ŝ+D₀} - Eġ_{Ŝ+D₀}‖_p ≤ C_p (1+u)/√W`. -/
def DiffCovarianceStatement : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    (∀ K₀ : ℝ, ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
      ∀ E ∈ bulkInterval κ,
      ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D‖ ≤ 1 →
      ∀ D₀ : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D₀‖ ≤ K₀ →
        let μ := layerLaw W b .separate
        let z := boundaryZ b E
        let K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
        let Y := (K⁻¹)ᴴ * S * K⁻¹
        let u := (W : ℝ)⁻¹ * Y.trace.re
        let G := fun ω => layerResolvent .separate E z X ω
        let Gh := fun (h : ℝ) ω => layerResolvent .separate E z (X - (h : ℂ) • S) ω
        HasDerivAt (fun h : ℝ => dcvCov μ (fun ω => (W : ℂ)⁻¹ * (D * Gh h ω).trace) (Gh h))
          (dcvCovDir μ D G (dcvHat S)) 0 ∧
        ‖dcvCovDir μ D G (dcvHat S)‖ ≤ C / (W : ℝ) ^ 2 * ‖Y‖ ∧
        C / (W : ℝ) ^ 2 * ‖Y‖ ≤ C * u / W ∧
        ‖dcvCovDir μ D G (dcvHat S + D₀)‖ ≤ C * (1 + u) / W) ∧
    (∀ K₀ p : ℝ, 1 ≤ p → ∃ (Cp : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
      ∀ E ∈ bulkInterval κ,
      ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D‖ ≤ 1 →
      ∀ D₀ : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D₀‖ ≤ K₀ →
        let μ := layerLaw W b .separate
        let z := boundaryZ b E
        let K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
        let Y := (K⁻¹)ᴴ * S * K⁻¹
        let u := (W : ℝ)⁻¹ * Y.trace.re
        let G := fun ω => layerResolvent .separate E z X ω
        let gdot := fun (P : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) ω =>
          -((W : ℂ)⁻¹ * (D * (G ω * P * G ω)).trace)
        (∀ᵐ ω ∂μ, HasDerivAt (fun h : ℝ =>
            (W : ℂ)⁻¹ * (D * layerResolvent .separate E z (X - (h : ℂ) • S) ω).trace)
          (gdot (dcvHat S) ω) 0) ∧
        eLpNorm (fun ω => gdot (dcvHat S) ω - ∫ ω', gdot (dcvHat S) ω' ∂μ) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (Cp / (W * Real.sqrt W) * Real.sqrt (Y * Y).trace.re) ∧
        Cp / (W * Real.sqrt W) * Real.sqrt (Y * Y).trace.re ≤ Cp * u / Real.sqrt W ∧
        eLpNorm (fun ω => gdot (dcvHat S + D₀) ω - ∫ ω', gdot (dcvHat S + D₀) ω' ∂μ)
            (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (Cp * (1 + u) / Real.sqrt W))

/-- `(h : ℂ) • S` is Hermitian for Hermitian `S` and real `h`. -/
theorem dcv_smul_isHermitian {n : Type*} {S : Matrix n n ℂ} (hS : S.IsHermitian) (h : ℝ) :
    ((h : ℂ) • S).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_smul, hS.eq, Complex.star_def, Complex.conj_ofReal]

/-- The covariance-derivative clause of `DiffCovarianceStatement`. -/
theorem dcv_cov_clause (hcount : ConditionalBlockGUECount) (hwl : WeightedLayerContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∀ K₀ : ℝ, ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
      ∀ E ∈ bulkInterval κ,
      ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D‖ ≤ 1 →
      ∀ D₀ : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D₀‖ ≤ K₀ →
        let μ := layerLaw W b .separate
        let z := boundaryZ b E
        let K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
        let Y := (K⁻¹)ᴴ * S * K⁻¹
        let u := (W : ℝ)⁻¹ * Y.trace.re
        let G := fun ω => layerResolvent .separate E z X ω
        let Gh := fun (h : ℝ) ω => layerResolvent .separate E z (X - (h : ℂ) • S) ω
        HasDerivAt (fun h : ℝ => dcvCov μ (fun ω => (W : ℂ)⁻¹ * (D * Gh h ω).trace) (Gh h))
          (dcvCovDir μ D G (dcvHat S)) 0 ∧
        ‖dcvCovDir μ D G (dcvHat S)‖ ≤ C / (W : ℝ) ^ 2 * ‖Y‖ ∧
        C / (W : ℝ) ^ 2 * ‖Y‖ ≤ C * u / W ∧
        ‖dcvCovDir μ D G (dcvHat S + D₀)‖ ≤ C * (1 + u) / W := by
  intro b hb0 hb1 κ hκ K₀
  obtain ⟨CT, W₁, hCT, hT⟩ := dcv_theta_eLpNorm hcount hwl hb0 hb1 hκ (q := 5) (by norm_num)
  obtain ⟨η₀, hη₀, hbulk⟩ := dcv_bulk hb0 hb1 hκ
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ := gaussianAbsorption_holds hcount b hb0 hb1 η₀ 3 hη₀
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = max K₀ 0 := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := hK₁ ▸ le_max_right _ _
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2560 * CT ^ 5 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨A * (1 + K₁), max W₁ ⌈4 / ε₁⌉₊, ?_⟩
  intro W hW hWW X S hX hS E hE D hD D₀ hD₀ μ z K Y u G Gh
  obtain ⟨hzim, hzM, -⟩ := hbulk E hE
  have hzpos : 0 < z.im := lt_of_lt_of_le hη₀ hzim
  have hKu : IsUnit K.det := dcv_K_isUnit hX hzpos
  have hSY : S = Kᴴ * Y * K := dcv_source_eq hKu
  have hYp : Y.PosSemidef := dcv_Y_posSemidef hS
  obtain ⟨hY0, hYn, -, -⟩ := dcv_Y_bounds hYp
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWu : Y.trace.re = W * u := by
    change Y.trace.re = W * ((W : ℝ)⁻¹ * Y.trace.re)
    field_simp
  have hu0 : 0 ≤ u := mul_nonneg (inv_nonneg.mpr hW'.le) hY0
  have hShat : (dcvHat S : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) =
      (dcvKh K)ᴴ * dcvHat Y * dcvKh K := dcv_hat_source_eq hSY
  have hmomT := hT W hW ((le_max_left _ _).trans hWW) X hX E hE
  have hinv0 := (habs W hW .separate X hX E z hzim hzM).1
  have hYh : ‖(dcvHat Y : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)‖ ≤ ‖Y‖ :=
    dcv_norm_hat_le Y
  have hCA0 := hCA.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the derivative
    have hW4 : ((4 : ℕ) : ℝ) ≤ ε₁ * W := by
      have h1 : 4 / ε₁ ≤ (W : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hWW)
      rw [div_le_iff₀ hε₁] at h1; push_cast; linarith
    have hXh : ∀ h : ℝ, (X - (h : ℂ) • S).IsHermitian := fun h =>
      hX.sub (dcv_smul_isHermitian hS.isHermitian h)
    exact dcv_hasDerivAt_cov_layer hW .separate E z X S D
      (fun h => (habs W hW .separate _ (hXh h) E z hzim hzM).1)
      (C4 := CA ^ 4) (fun h _ => tcv_moment (m := 4) (by norm_num) hCA0
        ((habs W hW .separate _ (hXh h) E z hzim hzM).2 _ (by norm_num) hW4))
  · -- `‖∂_h Cov‖ ≤ C W⁻² ‖Y‖`
    have hP : ∀ Gm : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ,
        ‖Gm * dcvHat S * Gm‖ ≤ ‖Y‖ * dcvTheta (dcvKh K) Gm ^ 2 := fun Gm => by
      rw [hShat]
      exact (dcv_factor_le (dcvKh K) (dcvHat Y) Gm).trans
        (mul_le_mul_of_nonneg_right hYh (sq_nonneg _))
    have hc := dcv_cov_core hW hb0 hb1 .separate hX E hzpos.le hD (dcvHat S) (dcvKh K)
      (norm_nonneg Y) hP hinv0 hCT hmomT
    refine hc.trans ?_
    have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hK₁0 : (1 : ℝ) ≤ 1 + K₁)
      (by positivity : 0 ≤ A / (W : ℝ) ^ 2 * ‖Y‖)
    calc 80 * ‖Y‖ / (W : ℝ) ^ 2 * (32 * CT ^ 5) = A / (W : ℝ) ^ 2 * ‖Y‖ * 1 := by rw [hA]; ring
      _ ≤ A / (W : ℝ) ^ 2 * ‖Y‖ * (1 + K₁) := this
      _ = A * (1 + K₁) / (W : ℝ) ^ 2 * ‖Y‖ := by ring
  · -- `C W⁻² ‖Y‖ ≤ C u / W`
    have hC0 : 0 ≤ A * (1 + K₁) := by positivity
    have hYW : ‖Y‖ ≤ W * u := hWu ▸ hYn
    calc A * (1 + K₁) / (W : ℝ) ^ 2 * ‖Y‖ ≤ A * (1 + K₁) / (W : ℝ) ^ 2 * (W * u) :=
          mul_le_mul_of_nonneg_left hYW (by positivity)
      _ = A * (1 + K₁) * u / W := by field_simp
  · -- the insertion variant
    have hD₀' : ‖D₀‖ ≤ K₁ := hD₀.trans (hK₁ ▸ le_max_left _ _)
    have hP : ∀ Gm : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ,
        ‖Gm * (dcvHat S + D₀) * Gm‖ ≤ (‖Y‖ + K₁) * dcvTheta (dcvKh K) Gm ^ 2 := fun Gm => by
      rw [hShat]
      exact (dcv_dir_le (dcvKh K) (dcvHat Y) D₀ Gm).trans
        (mul_le_mul_of_nonneg_right (add_le_add hYh hD₀') (sq_nonneg _))
    have hc := dcv_cov_core hW hb0 hb1 .separate hX E hzpos.le hD (dcvHat S + D₀) (dcvKh K)
      (add_nonneg (norm_nonneg Y) hK₁0) hP hinv0 hCT hmomT
    refine hc.trans ?_
    have hYW : ‖Y‖ ≤ W * u := hWu ▸ hYn
    have e1 : 80 * (‖Y‖ + K₁) / (W : ℝ) ^ 2 * (32 * CT ^ 5) = A * (‖Y‖ + K₁) / (W : ℝ) ^ 2 := by
      rw [hA]; ring
    rw [e1, div_le_div_iff₀ (by positivity) hW']
    have h1 : ‖Y‖ + K₁ ≤ W * u + K₁ := by linarith
    have h2 : (W * u + K₁) * W ≤ (1 + K₁) * (1 + u) * W ^ 2 := by
      have : K₁ * W ≤ K₁ * W ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hK₁0
      nlinarith [mul_nonneg hK₁0 hu0, mul_nonneg (mul_nonneg hK₁0 hu0) (sq_nonneg (W : ℝ))]
    calc A * (‖Y‖ + K₁) * W ≤ A * (W * u + K₁) * W := by gcongr
      _ = A * ((W * u + K₁) * W) := by ring
      _ ≤ A * ((1 + K₁) * (1 + u) * W ^ 2) := mul_le_mul_of_nonneg_left h2 hA0
      _ = A * (1 + K₁) * (1 + u) * W ^ 2 := by ring

/-- **The differentiated-covariance lemma**, from `ConditionalBlockGUECount` (through the
Gaussian absorption lemma), `GaussianLpGradient` and `WeightedLayerContract` (`moments` field
only). Constants: `C = 2560 C_Θ⁵ (1 + max K₀ 0)` with `C_Θ` the `L⁵` bound of
`Θ(𝒢) = ‖𝒢‖ + ‖𝒢𝒦*‖ + ‖𝒦𝒢‖` (`dcv_theta_eLpNorm`), `W₀ = max W₀(Θ, 5) ⌈4/ε₁⌉`;
`C_p = 32 C_g √p C_{Θ,3p}³ (2 + 3 max K₀ 0)`, `W₀(p) = W₀(Θ, 3p)`. -/
theorem diffCovariance_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) (hwl : WeightedLayerContract) :
    DiffCovarianceStatement := by
  intro b hb0 hb1 κ hκ
  exact ⟨dcv_cov_clause hcount hwl b hb0 hb1 κ hκ, dcv_noise_clause hcount hgrad hwl b hb0 hb1 κ hκ⟩

end BlockBand.Layers
