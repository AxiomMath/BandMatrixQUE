module

public import BlockBand.Endpoints.Clock.CommonPortRatiosEstimate
public import BlockBand.Endpoints.Clock.CommonPortRatiosWeak

/-!
# Uniform comparison of finite families of positive common-port clocks, and their ratios

We compare the joint laws of finitely many positive common-port clocks, and of their ratios, with
their Gaussian reference laws.

* `commonPort_clockFamily_comparison` (the joint comparison): for `n` positive old
  matrices `P_i ⪰ 0` with `Re Tr P_i ≤ K T`, `T > 0`, the clock vectors
  `(Re (Lg)*P_i(Lg)/(γT))_i` and `(Re h*P_ih/T)_i` are compared against a fixed continuous
  bounded test `ψ` on `ℝⁿ`, uniformly in `W ≥ W₀`, `δ ≤ δ₀`, `X`, `e` and the matrices.
  Proof: the positive combinations `F = Σ λ_i P_i/(γT)` give, by `commonPort_laplace_estimate`,
  the joint Laplace transforms at every `λ ∈ [0,N]ⁿ` to within `C(δ+W⁻²+W^{-1/2}) n N K/γ`; the
  reference first moments are `Re Tr P_i/T ≤ K`; `exists_laplace_comparison` concludes.
* `commonPort_ratio_comparison` (small denominators): for a measurable bounded
  function `G` of the probe vector which, on `{Re v*P₀v ≥ u s}`, is a fixed continuous function
  `ψ_u` of the clocks normalized by any scale `s > 0` (the ratio functionals), the two laws of
  `G` are compared uniformly. The denominator is paid by `1_{x<u} ≤ e·e^{-x/u}`, the Gaussian
  bound `E_h exp(-Re h*P₀h/(uT)) ≤ (1 + 1/u)⁻¹ ≤ u` (trace-one covariance) and its transfer to
  the probe side by the Laplace estimate at `a = 1/u`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal ComplexOrder Matrix

/-- `W^{-1/2} = (√W)⁻¹`. -/
theorem CommonPortRatios.rpow_neg_half_eq (W : ℝ) (hW : 0 ≤ W) : W ^ (-(1 : ℝ) / 2) = (Real.sqrt W)⁻¹ := by
  rw [neg_div, Real.rpow_neg hW, ← Real.sqrt_eq_rpow]

/-- The rate `C(δ + W⁻² + W^{-1/2})` is small for small `δ` and large `W`. -/
theorem CommonPortRatios.exists_small_rate {C t : ℝ} (hC : 0 ≤ C) (ht : 0 < t) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ W₀ : ℕ, 0 < W₀ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ δ : ℝ, δ ≤ δ₀ →
      C * (δ + 1 / (W : ℝ) ^ 2 + (W : ℝ) ^ (-(1 : ℝ) / 2)) ≤ t := by
  set s := t / (3 * (C + 1))
  have hs : 0 < s := by positivity
  refine ⟨s, hs, ⌈1 / s ^ 2⌉₊ + 1, Nat.succ_pos _, fun W hW δ hδ => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (Nat.le_add_left 1 _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWs : 1 / s ^ 2 ≤ W := by
    have : (⌈1 / s ^ 2⌉₊ : ℝ) + 1 ≤ W := by exact_mod_cast hW
    linarith [Nat.le_ceil (1 / s ^ 2)]
  have hsq : 1 / s ≤ Real.sqrt W := by
    rw [show 1 / s = Real.sqrt ((1 / s) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by rw [div_pow, one_pow]; exact hWs)
  have hsqpos : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
  have hr : (W : ℝ) ^ (-(1 : ℝ) / 2) ≤ s := by
    rw [CommonPortRatios.rpow_neg_half_eq _ hW0.le]
    rw [inv_le_comm₀ hsqpos hs, ← one_div]; exact hsq
  have hr2 : 1 / (W : ℝ) ^ 2 ≤ (W : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [CommonPortRatios.rpow_neg_half_eq _ hW0.le, one_div]
    refine inv_anti₀ hsqpos ?_
    calc Real.sqrt W ≤ W := by
          rw [Real.sqrt_le_left (by linarith)]; nlinarith
      _ ≤ (W : ℝ) ^ 2 := by nlinarith
  have hsum : δ + 1 / (W : ℝ) ^ 2 + (W : ℝ) ^ (-(1 : ℝ) / 2) ≤ 3 * s := by linarith
  calc C * (δ + 1 / (W : ℝ) ^ 2 + (W : ℝ) ^ (-(1 : ℝ) / 2)) ≤ C * (3 * s) :=
        mul_le_mul_of_nonneg_left hsum hC
    _ = t * (C / (C + 1)) := by simp only [s]; field_simp
    _ ≤ t * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one (by linarith)).mpr (by linarith)) ht.le
    _ = t := mul_one t

/-- Positive real combinations of positive semidefinite matrices. -/
theorem CommonPortRatios.posSemidef_sum_real_smul {ι n : Type*} [Fintype ι] [Fintype n]
    (c : n → ℝ) (hc : ∀ i, 0 ≤ c i) (P : n → Matrix ι ι ℂ) (hP : ∀ i, (P i).PosSemidef) :
    (∑ i, ((c i : ℝ) : ℂ) • P i).PosSemidef :=
  posSemidef_sum _ fun i _ => (hP i).smul (Complex.zero_le_real.mpr (hc i))

/-- `Re Tr Σ c_i P_i = Σ c_i Re Tr P_i`. -/
theorem CommonPortRatios.re_trace_sum_real_smul {ι n : Type*} [Fintype ι] [Fintype n]
    (c : n → ℝ) (P : n → Matrix ι ι ℂ) :
    (∑ i, ((c i : ℝ) : ℂ) • P i).trace.re = ∑ i, c i * (P i).trace.re := by
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- **Joint comparison of a finite family of positive common-port clocks**, from
`CommonPortMeanContract` only. Fixed first: `b ∈ (0,1/2)`, `κ > 0`,
`n`, a continuous `ψ : ℝⁿ → ℝ` with `|ψ| ≤ M`, `K` and `ε > 0`. Then `δ₀ > 0` and `W₀`; for
`W ≥ W₀`, Hermitian `X`, `e ∈ bulkInterval κ` with `δ ≤ δ₀`, all `P_i ⪰ 0`, `T > 0` with
`Re Tr P_i ≤ K T`:
`|E_{ω,g} ψ((Re (Lg)*P_i(Lg)/(γT))_i) - E_h ψ((Re h*P_ih/T)_i)| ≤ ε`. -/
theorem commonPort_clockFamily_comparison (hc : CommonPortMeanContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (ψ : (Fin n → ℝ) → ℝ) (hψ : Continuous ψ)
    {M : ℝ} (hM : ∀ x, |ψ x| ≤ M) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ e ∈ bulkInterval κ, matchedDistance b e X ≤ δ₀ →
      ∀ P : Fin n → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, (∀ i, (P i).PosSemidef) →
      ∀ T : ℝ, 0 < T → (∀ i, (P i).trace.re ≤ K * T) →
        |(∫ x, ψ (fun i => quadForm (P i) (commonPortProbe b e X x) / (commonPortGamma b * T))
            ∂commonPortProbeLaw W b) -
          ∫ h, ψ (fun i => quadForm (P i) h / T) ∂circularVectorLaw (Fin 2 × Fin W)| ≤ ε := by
  set K' := max K 0
  obtain ⟨η, hη, N, hN1, hcmp⟩ := exists_laplace_comparison n ψ hψ hM K' hε
  obtain ⟨δ₁, C, W₁, hδ₁, hC, hlap⟩ := commonPort_laplace_estimate hc hb0 hb1 hκ
  set γ := commonPortGamma b
  have hγ : 0 < γ := CommonPortRatios.commonPortGamma_pos hb1
  set Λ := n * N * K' / γ
  have hΛ : 0 ≤ Λ := by have : 0 ≤ K' := le_max_right _ _; positivity
  obtain ⟨δ₂, hδ₂, W₂, -, hrate⟩ := CommonPortRatios.exists_small_rate (C := C * Λ) (mul_nonneg hC hΛ) hη
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max W₁ W₂, ?_⟩
  intro W hW hWW X hX e he hδ P hP T hT hPK
  have hμ := commonPortRatios_isProbabilityMeasure_probeLaw W b
  have hδ0 : 0 ≤ matchedDistance b e X := le_max_of_le_left (norm_nonneg _)
  have hPtr : ∀ i, 0 ≤ (P i).trace.re := fun i => (Complex.nonneg_iff.mp (hP i).trace_nonneg).1
  have hPK' : ∀ i, (P i).trace.re ≤ K' * T := fun i =>
    (hPK i).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hT.le)
  have hqm : ∀ i, Measurable (fun v : Fin 2 × Fin W → ℂ => quadForm (P i) v) := fun i =>
    (continuous_quadForm.comp (continuous_const.prodMk continuous_id)).measurable
  refine hcmp (commonPortProbeLaw W b) (circularVectorLaw (Fin 2 × Fin W)) hμ inferInstance
    (fun x i => quadForm (P i) (commonPortProbe b e X x) / (γ * T))
    (fun h i => quadForm (P i) h / T)
    (measurable_pi_iff.mpr fun i =>
      ((hqm i).comp (CommonPortRatios.measurable_commonPortProbe b e X)).div_const _)
    (measurable_pi_iff.mpr fun i => (hqm i).div_const _)
    (fun x i => div_nonneg (CommonPortRatios.quadForm_nonneg_of_posSemidef (hP i) _) (by positivity))
    (fun h i => div_nonneg (CommonPortRatios.quadForm_nonneg_of_posSemidef (hP i) _) hT.le)
    (fun i => (integrable_quadForm_circular (P i)).div_const T)
    (fun i => by
      rw [integral_div, integral_quadForm_circular, div_le_iff₀ hT]; exact hPK' i) ?_
  intro lam hl hlN
  set c : Fin n → ℝ := fun i => lam i / (γ * T)
  have hc0 : ∀ i, 0 ≤ c i := fun i => div_nonneg (hl i) (by positivity)
  set F := ∑ i, ((c i : ℝ) : ℂ) • P i
  have hF : F.PosSemidef := CommonPortRatios.posSemidef_sum_real_smul c hc0 P hP
  have e1 : ∀ v, ∑ i, lam i * (quadForm (P i) v / (γ * T)) = quadForm F v := by
    intro v; rw [CommonPortRatios.quadForm_sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [c]; ring
  have e2 : ∀ v, ∑ i, lam i * (quadForm (P i) v / T) = γ * quadForm F v := by
    intro v; rw [CommonPortRatios.quadForm_sum_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [c]; field_simp
  simp_rw [e1, e2]
  have hTrF : F.trace.re ≤ Λ := by
    rw [CommonPortRatios.re_trace_sum_real_smul]
    calc ∑ i, c i * (P i).trace.re ≤ ∑ _i : Fin n, N / (γ * T) * (K' * T) :=
          Finset.sum_le_sum fun i _ => mul_le_mul (div_le_div_of_nonneg_right (hlN i)
            (by positivity)) (hPK' i) (hPtr i) (by positivity)
      _ = Λ := by
          have := hT.ne'; have := hγ.ne'
          simp only [Λ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hrate' := hrate W (le_of_max_le_right hWW) _ (le_trans hδ (min_le_right _ _))
  refine (hlap W hW (le_of_max_le_left hWW) X hX e he (le_trans hδ (min_le_left _ _)) F hF).trans ?_
  have hr0 : 0 ≤ C * (matchedDistance b e X + 1 / (W : ℝ) ^ 2 + (W : ℝ) ^ (-(1 : ℝ) / 2)) := by
    positivity
  calc C * (matchedDistance b e X + 1 / (W : ℝ) ^ 2 + (W : ℝ) ^ (-(1 : ℝ) / 2)) * F.trace.re
      ≤ C * (matchedDistance b e X + 1 / (W : ℝ) ^ 2 + (W : ℝ) ^ (-(1 : ℝ) / 2)) * Λ :=
        mul_le_mul_of_nonneg_left hTrF hr0
    _ = C * Λ * (matchedDistance b e X + 1 / (W : ℝ) ^ 2 + (W : ℝ) ^ (-(1 : ℝ) / 2)) := by ring
    _ ≤ η := hrate'

/-- The small-ball Gaussian bound in clock units: for `P ⪰ 0` with `T = Re Tr P > 0` and
`u > 0`, `E_h exp(-(Re h*Ph/T)/u) ≤ u` (from `E e^{-sX̃₀} ≤ (1+s)⁻¹`). -/
theorem integral_exp_neg_clock_div_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) {T u : ℝ} (hT : T = P.trace.re) (hT0 : 0 < T)
    (hu : 0 < u) :
    ∫ h, Real.exp (-(quadForm P h / T / u)) ∂circularVectorLaw ι ≤ u := by
  set A : Matrix ι ι ℂ := ((1 / (T * u) : ℝ) : ℂ) • P
  have hA : A.PosSemidef := hP.smul (Complex.zero_le_real.mpr (by positivity))
  have hq : ∀ h, quadForm P h / T / u = quadForm A h := by
    intro h; rw [CommonPortRatios.quadForm_smul_real]; field_simp
  have htr : A.trace.re = 1 / u := by
    simp only [A]
    rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, ← hT]
    field_simp
  simp_rw [hq]
  refine (integral_exp_neg_quadForm_le_inv_one_add_trace hA).trans ?_
  rw [htr, inv_le_iff_one_le_mul₀ (by positivity)]
  rw [mul_add, mul_one, mul_one_div_cancel hu.ne']
  linarith

/-- **Ratio comparison with small denominators**, from `CommonPortMeanContract` only. Fixed first: `b`, `κ`, `m`, a family `ψ_u` (`u > 0`) of continuous
tests on `ℝ^{m+1}` bounded by `M`, `K` and `ε > 0`. Then `δ₀ > 0`, `W₀`; for `W ≥ W₀`,
Hermitian `X`, `e ∈ bulkInterval κ` with `δ ≤ δ₀`, all `P_i ⪰ 0` with `T = Re Tr P₀ > 0`,
`Re Tr P_i ≤ K T`, and every measurable `G` with `|G| ≤ M` which equals
`ψ_u((Re v*P_iv/s)_i)` wherever `Re v*P₀v/s ≥ u` (any scale `s > 0`, any `u > 0`):
`|E_{ω,g} G(Lg) - E_h G(h)| ≤ ε`. -/
theorem commonPort_ratio_comparison (hc : CommonPortMeanContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (m : ℕ) (ψ : ℝ → (Fin (m + 1) → ℝ) → ℝ)
    (hψc : ∀ u, 0 < u → Continuous (ψ u)) {M : ℝ} (hψM : ∀ u x, |ψ u x| ≤ M) (K : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ e ∈ bulkInterval κ, matchedDistance b e X ≤ δ₀ →
      ∀ P : Fin (m + 1) → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, (∀ i, (P i).PosSemidef) →
      0 < (P 0).trace.re → (∀ i, (P i).trace.re ≤ K * (P 0).trace.re) →
      ∀ G : (Fin 2 × Fin W → ℂ) → ℝ, Measurable G → (∀ v, |G v| ≤ M) →
      (∀ u, 0 < u → ∀ v (s : ℝ), 0 < s → u ≤ quadForm (P 0) v / s →
        G v = ψ u (fun i => quadForm (P i) v / s)) →
        |(∫ x, G (commonPortProbe b e X x) ∂commonPortProbeLaw W b) -
          ∫ h, G h ∂circularVectorLaw (Fin 2 × Fin W)| ≤ ε := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hψM 1 0)
  set E := Real.exp 1
  have hE : 0 < E := Real.exp_pos 1
  set q := M * E
  have hq : 0 ≤ q := by positivity
  set u := ε / (16 * (q + 1))
  have hu : 0 < u := by positivity
  set t := ε / (8 * (q + 1))
  have ht : 0 < t := by positivity
  obtain ⟨δ₁, hδ₁, W₁, hfam⟩ := commonPort_clockFamily_comparison hc hb0 hb1 hκ (m + 1) (ψ u)
    (hψc u hu) (hψM u) K (half_pos hε)
  obtain ⟨δ₂, C, W₂, hδ₂, hC, hlap⟩ := commonPort_laplace_estimate hc hb0 hb1 hκ
  set γ := commonPortGamma b
  have hγ : 0 < γ := CommonPortRatios.commonPortGamma_pos hb1
  obtain ⟨δ₃, hδ₃, W₃, -, hrate⟩ := CommonPortRatios.exists_small_rate (C := C / (γ * u)) (by positivity) ht
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), max W₁ (max W₂ W₃), ?_⟩
  intro W hW hWW X hX e he hδ P hP hT hPK G hG hGM hagree
  have hμ := commonPortRatios_isProbabilityMeasure_probeLaw W b
  set T := (P 0).trace.re with hTdef
  set μ := commonPortProbeLaw W b
  set ν := circularVectorLaw (Fin 2 × Fin W)
  have hW1 : W₁ ≤ W := le_of_max_le_left hWW
  have hW2 : W₂ ≤ W := le_trans (le_max_left _ _) (le_of_max_le_right hWW)
  have hW3 : W₃ ≤ W := le_trans (le_max_right _ _) (le_of_max_le_right hWW)
  have hδ1 : matchedDistance b e X ≤ δ₁ := le_trans hδ (min_le_left _ _)
  have hδ2 : matchedDistance b e X ≤ δ₂ := le_trans hδ (le_trans (min_le_right _ _)
    (min_le_left _ _))
  have hδ3 : matchedDistance b e X ≤ δ₃ := le_trans hδ (le_trans (min_le_right _ _)
    (min_le_right _ _))
  have hqm : ∀ i, Measurable (fun v : Fin 2 × Fin W → ℂ => quadForm (P i) v) := fun i =>
    (continuous_quadForm.comp (continuous_const.prodMk continuous_id)).measurable
  have hpm := CommonPortRatios.measurable_commonPortProbe b e X
  -- the joint comparison
  have hB := hfam W hW hW1 X hX e he hδ1 P hP T hT hPK
  -- the exponential weights
  set wL : LayerSample W .common × (Fin 1 × Fin W → ℂ) → ℝ :=
    fun x => Real.exp (-(quadForm (P 0) (commonPortProbe b e X x) / (γ * T) / u))
  set wR : (Fin 2 × Fin W → ℂ) → ℝ := fun h => Real.exp (-(quadForm (P 0) h / T / u))
  have hwL : Integrable wL μ := CommonPortRatios.integrable_of_abs_le μ
    (Real.continuous_exp.measurable.comp ((((hqm 0).comp hpm).div_const _).div_const _).neg) 1
    fun x => by
      simp only [wL]
      rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      exact div_nonneg (div_nonneg (CommonPortRatios.quadForm_nonneg_of_posSemidef (hP 0) _) (by positivity))
        hu.le
  have hwR : Integrable wR ν := CommonPortRatios.integrable_of_abs_le ν
    (Real.continuous_exp.measurable.comp (((hqm 0).div_const _).div_const _).neg) 1
    fun h => by
      simp only [wR]
      rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      exact div_nonneg (div_nonneg (CommonPortRatios.quadForm_nonneg_of_posSemidef (hP 0) _) hT.le) hu.le
  -- bound for the reference weight
  have hI : ∫ h, wR h ∂ν ≤ u := integral_exp_neg_clock_div_le (hP 0) hTdef hT hu
  -- transfer to the probe weight by the Laplace estimate
  have hJ : ∫ x, wL x ∂μ ≤ u + t := by
    set F : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := ((1 / (γ * T * u) : ℝ) : ℂ) • P 0
    have hF : F.PosSemidef := (hP 0).smul (Complex.zero_le_real.mpr (by positivity))
    have hFtr : F.trace.re = 1 / (γ * u) := by
      simp only [F]
      rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, ← hTdef]
      field_simp
    have hlap' := hlap W hW hW2 X hX e he hδ2 F hF
    have e1 : (fun x => Real.exp (-quadForm F (commonPortProbe b e X x))) = wL := by
      funext x; simp only [wL, F]; rw [CommonPortRatios.quadForm_smul_real]; congr 2; field_simp
    have e2 : (fun h => Real.exp (-(γ * quadForm F h))) = wR := by
      funext h; simp only [wR, F]; rw [CommonPortRatios.quadForm_smul_real]; congr 2; field_simp
    rw [e1, e2, hFtr] at hlap'
    have hr := hrate W hW3 _ hδ3
    have : C * (matchedDistance b e X + 1 / (W : ℝ) ^ 2 + (W : ℝ) ^ (-(1 : ℝ) / 2)) *
        (1 / (γ * u)) = C / (γ * u) *
          (matchedDistance b e X + 1 / (W : ℝ) ^ 2 + (W : ℝ) ^ (-(1 : ℝ) / 2)) := by ring
    rw [this] at hlap'
    linarith [(abs_le.mp hlap').2]
  -- the two cutoff errors
  have hGL : Integrable (fun x => G (commonPortProbe b e X x)) μ :=
    CommonPortRatios.integrable_of_abs_le μ (hG.comp hpm) M fun x => hGM _
  have hGR : Integrable G ν := CommonPortRatios.integrable_of_abs_le ν hG M hGM
  have hψL : Integrable (fun x => ψ u (fun i => quadForm (P i) (commonPortProbe b e X x) /
      (γ * T))) μ := CommonPortRatios.integrable_of_abs_le μ ((hψc u hu).measurable.comp
        (measurable_pi_iff.mpr fun i => ((hqm i).comp hpm).div_const _)) M fun x => hψM _ _
  have hψR : Integrable (fun h => ψ u (fun i => quadForm (P i) h / T)) ν :=
    CommonPortRatios.integrable_of_abs_le ν ((hψc u hu).measurable.comp
      (measurable_pi_iff.mpr fun i => (hqm i).div_const _)) M fun h => hψM _ _
  have hA : |(∫ x, G (commonPortProbe b e X x) ∂μ) -
      ∫ x, ψ u (fun i => quadForm (P i) (commonPortProbe b e X x) / (γ * T)) ∂μ| ≤
      2 * M * E * ∫ x, wL x ∂μ := by
    rw [← integral_sub hGL hψL, ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hwL.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact CommonPortRatios.abs_sub_le_two_mul_exp_neg hu (hGM _) (hψM _ _)
      (hagree u hu _ (γ * T) (by positivity))
  have hC' : |(∫ h, ψ u (fun i => quadForm (P i) h / T) ∂ν) - ∫ h, G h ∂ν| ≤
      2 * M * E * ∫ h, wR h ∂ν := by
    rw [abs_sub_comm, ← integral_sub hGR hψR, ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hwR.const_mul _) (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs]
    exact CommonPortRatios.abs_sub_le_two_mul_exp_neg hu (hGM _) (hψM _ _) (hagree u hu _ T hT)
  -- assemble
  have hq2 : 2 * q * (2 * u + t) ≤ ε / 2 := by
    have : 2 * q * (2 * u + t) = ε / 2 * (q / (q + 1)) := by
      simp only [u, t]; field_simp; ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by linarith)).mpr (by linarith))
  have hJ0 : 0 ≤ ∫ x, wL x ∂μ := integral_nonneg fun x => (Real.exp_pos _).le
  have hI0 : 0 ≤ ∫ h, wR h ∂ν := integral_nonneg fun h => (Real.exp_pos _).le
  calc |(∫ x, G (commonPortProbe b e X x) ∂μ) - ∫ h, G h ∂ν|
      ≤ |(∫ x, G (commonPortProbe b e X x) ∂μ) -
          ∫ x, ψ u (fun i => quadForm (P i) (commonPortProbe b e X x) / (γ * T)) ∂μ| +
        |(∫ x, ψ u (fun i => quadForm (P i) (commonPortProbe b e X x) / (γ * T)) ∂μ) -
          ∫ h, ψ u (fun i => quadForm (P i) h / T) ∂ν| +
        |(∫ h, ψ u (fun i => quadForm (P i) h / T) ∂ν) - ∫ h, G h ∂ν| := by
        have h1 := abs_sub_le (∫ x, G (commonPortProbe b e X x) ∂μ)
          (∫ x, ψ u (fun i => quadForm (P i) (commonPortProbe b e X x) / (γ * T)) ∂μ)
          (∫ h, G h ∂ν)
        have h2 := abs_sub_le
          (∫ x, ψ u (fun i => quadForm (P i) (commonPortProbe b e X x) / (γ * T)) ∂μ)
          (∫ h, ψ u (fun i => quadForm (P i) h / T) ∂ν) (∫ h, G h ∂ν)
        linarith
    _ ≤ 2 * M * E * ∫ x, wL x ∂μ + ε / 2 + 2 * M * E * ∫ h, wR h ∂ν := by
        gcongr
    _ ≤ 2 * q * (u + t) + ε / 2 + 2 * q * u := by
        have h2q : 0 ≤ 2 * q := by positivity
        have := mul_le_mul_of_nonneg_left hJ h2q
        have := mul_le_mul_of_nonneg_left hI h2q
        simp only [q] at *
        nlinarith
    _ ≤ ε := by nlinarith

end BlockBand.Endpoints.Clock
