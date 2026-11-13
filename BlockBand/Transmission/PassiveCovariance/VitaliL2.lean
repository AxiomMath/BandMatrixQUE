module

public import BlockBand.Transmission.PassiveCovariance.Reduction

/-!
# Vitali convergence from `L²` bounds, and the covariance as `E[b₁₂b₃₄] - E b₁₂ E b₃₄`

* `unifIntegrable_of_eLpNorm_two`, `tendsto_integral_of_ae_of_eLpNorm_two`: a.e. convergence
  plus a uniform `L²` bound gives convergence of the integrals (Vitali, Mathlib
  `tendsto_Lp_finite_of_tendsto_ae`).
* `eLpNorm_pow_le`, `eLpNorm_two_le_of_pow_bound`: `L²` bounds from moments of a dominating
  function.
* `bilinear_matrixExpect`, `bilinearCovariance_eq`: `u*(EU)v = E[u*Uv]` and
  `Cov = E[b₁₂b₃₄] - E[b₁₂]E[b₃₄]` under integrability.
* `norm_entry_le`, `norm_freshU_le`: `|M_ij| ≤ ‖M‖`, `‖LL*‖ ≤ ‖L‖²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

section VitaliPart
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem lintegral_sq_eq_eLpNorm {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hf
  simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] at h2
  exact h2.symm

/-- Uniform `L²` bounds give uniform integrability in `L¹`. -/
theorem unifIntegrable_of_eLpNorm_two {f : ℕ → Ω → ℂ} (hf : ∀ n, Measurable (f n))
    {K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ n, eLpNorm (f n) 2 μ ≤ K) : UnifIntegrable f 1 μ := by
  refine unifIntegrable_of le_rfl ENNReal.one_ne_top (fun n => (hf n).aestronglyMeasurable)
    fun ε hε => ?_
  have hK2 : K ^ 2 ≠ ∞ := ENNReal.pow_ne_top hK
  by_cases hεtop : ε = ∞
  · exact ⟨1, fun n => by rw [hεtop]; exact le_top⟩
  set C : ℝ≥0 := (K ^ 2 / ε).toNNReal + 1
  have hCpos : (0 : ℝ≥0∞) < C := by positivity
  have hC : K ^ 2 / ε ≤ C := by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal (ENNReal.div_ne_top hK2 hε.ne')]
    exact le_self_add
  refine ⟨C, fun n => ?_⟩
  have hs : MeasurableSet {x | C ≤ ‖f n x‖₊} := measurableSet_le measurable_const (hf n).nnnorm
  rw [eLpNorm_one_eq_lintegral_enorm (((hf n).indicator hs).aestronglyMeasurable)]
  calc ∫⁻ x, ‖({x | C ≤ ‖f n x‖₊}.indicator (f n)) x‖ₑ ∂μ
      ≤ ∫⁻ x, ‖f n x‖ₑ ^ 2 / C ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : C ≤ ‖f n x‖₊
        · rw [Set.indicator_of_mem (by exact hx)]
          rw [ENNReal.le_div_iff_mul_le (Or.inl hCpos.ne') (Or.inl ENNReal.coe_ne_top), pow_two]
          gcongr
          rw [enorm_eq_nnnorm]; exact_mod_cast hx
        · rw [Set.indicator_of_notMem (by exact hx), enorm_zero]; exact zero_le
    _ = (∫⁻ x, ‖f n x‖ₑ ^ 2 ∂μ) / C := by
        simp_rw [div_eq_mul_inv]; rw [lintegral_mul_const' _ _ (by simpa using hCpos.ne')]
    _ ≤ K ^ 2 / C := by
        rw [lintegral_sq_eq_eLpNorm (hf n).aestronglyMeasurable]
        gcongr; exact h n
    _ ≤ ε := by
        rw [ENNReal.div_le_iff hCpos.ne' ENNReal.coe_ne_top]
        rw [ENNReal.div_le_iff hε.ne' hεtop] at hC
        rwa [mul_comm]

/-- **Vitali from `L²` bounds**: a.e. convergence and uniform `L²` bounds give convergence of
the integrals. -/
theorem tendsto_integral_of_ae_of_eLpNorm_two [IsFiniteMeasure μ] {f : ℕ → Ω → ℂ} {g : Ω → ℂ}
    (hf : ∀ n, Measurable (f n)) {K : ℝ≥0∞}
    (hK : K ≠ ∞) (h : ∀ n, eLpNorm (f n) 2 μ ≤ K) (hgK : eLpNorm g 2 μ ≤ K)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hg2 : MemLp g 2 μ := lt_of_le_of_lt hgK hK.lt_top
  have hg1 : MemLp g 1 μ := hg2.mono_exponent one_le_two
  have hfi : ∀ n, Integrable (f n) μ := fun n =>
    (MemLp.mono_exponent (lt_of_le_of_lt (h n) hK.lt_top : MemLp (f n) 2 μ) one_le_two).integrable le_rfl
  have hv := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun n => (hf n).aestronglyMeasurable) hg1
    (unifIntegrable_of_eLpNorm_two hf hK h) hae
  exact tendsto_integral_of_L1' g (Eventually.of_forall hfi) hv

theorem eLpNorm_pow_le {g : Ω → ℝ} (hg0 : ∀ ω, 0 ≤ g ω) (hgm : AEStronglyMeasurable g μ)
    (k : ℕ) (hk : 1 ≤ k) {C : ℝ} (h : eLpNorm g (ENNReal.ofReal (2 * k)) μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun ω => g ω ^ k) 2 μ ≤ ENNReal.ofReal C ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have e := eLpNorm_norm_rpow (p := 2) g hgm hk0
  have e1 : (fun x => ‖g x‖ ^ (k : ℝ)) = fun ω => g ω ^ k := by
    funext x; rw [Real.norm_of_nonneg (hg0 x), Real.rpow_natCast]
  have e2 : (2 : ℝ≥0∞) * ENNReal.ofReal k = ENNReal.ofReal (2 * k) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [e1, e2, ENNReal.rpow_natCast] at e
  rw [e]
  exact pow_le_pow_left₀ zero_le h k

end VitaliPart

section
variable {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] {μ : Measure Ω}

theorem bilinear_matrixExpect (U : Ω → Matrix n n ℂ) (u v : n → ℂ)
    (hU : ∀ i j, Integrable (fun ω => U ω i j) μ) :
    bilinear u (matrixExpect μ U) v = ∫ ω, bilinear u (U ω) v ∂μ := by
  simp only [bilinear, dotProduct, mulVec, matrixExpect, Matrix.of_apply, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    ((hU i j).mul_const _).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => ((hU i j).mul_const _).const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_const]

/-- `Cov = E[b₁₂b₃₄] - E[b₁₂]E[b₃₄]`. -/
theorem bilinearCovariance_eq [IsProbabilityMeasure μ] (U : Ω → Matrix n n ℂ)
    (v₁ v₂ v₃ v₄ : n → ℂ) (hU : ∀ i j, Integrable (fun ω => U ω i j) μ)
    (h12 : Integrable (fun ω => bilinear v₁ (U ω) v₂) μ)
    (h34 : Integrable (fun ω => bilinear v₃ (U ω) v₄) μ)
    (hp : Integrable (fun ω => bilinear v₁ (U ω) v₂ * bilinear v₃ (U ω) v₄) μ) :
    bilinearCovariance μ U v₁ v₂ v₃ v₄ =
      (∫ ω, bilinear v₁ (U ω) v₂ * bilinear v₃ (U ω) v₄ ∂μ) -
        (∫ ω, bilinear v₁ (U ω) v₂ ∂μ) * ∫ ω, bilinear v₃ (U ω) v₄ ∂μ := by
  rw [bilinearCovariance]
  simp only [bilinear_sub, bilinear_matrixExpect U _ _ hU]
  set m₁ := ∫ ω, bilinear v₁ (U ω) v₂ ∂μ
  set m₂ := ∫ ω, bilinear v₃ (U ω) v₄ ∂μ
  have e : (fun ω => (bilinear v₁ (U ω) v₂ - m₁) * (bilinear v₃ (U ω) v₄ - m₂)) = fun ω =>
      bilinear v₁ (U ω) v₂ * bilinear v₃ (U ω) v₄ - m₂ * bilinear v₁ (U ω) v₂ -
        m₁ * bilinear v₃ (U ω) v₄ + m₁ * m₂ := by funext ω; ring
  rw [e, integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
    integral_const]
  · simp; ring
  all_goals first
    | exact hp | exact h12.const_mul _ | exact h34.const_mul _ | exact integrable_const _
    | exact hp.sub (h12.const_mul _) | exact (hp.sub (h12.const_mul _)).sub (h34.const_mul _)
end

section Conv
variable {W : ℕ}

theorem norm_entry_le (M : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) : ‖M i j‖ ≤ ‖M‖ := by
  have h := norm_bilinear_le (Pi.single i 1) M (Pi.single j 1)
  have hv : ∀ k : Fin W, vecNorm (Pi.single k (1 : ℂ)) = 1 := fun k => by
    rw [vecNorm, Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (by simp)]
    simp
  have hb : bilinear (Pi.single i 1) M (Pi.single j 1) = M i j := by
    simp [bilinear, mulVec, dotProduct, Pi.single_apply]
  rwa [hb, hv, hv, mul_one, one_mul] at h

theorem norm_freshU_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ‖freshU b E X ω‖ ≤ ‖freshL b E X ω‖ ^ 2 := by
  rw [freshU, pow_two]
  refine (Matrix.l2_opNorm_mul _ _).trans (le_of_eq ?_)
  rw [Matrix.l2_opNorm_conjTranspose]

theorem eLpNorm_two_le_of_pow_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ) {g : Ω → ℝ} (hg0 : ∀ ω, 0 ≤ g ω)
    (hgm : AEStronglyMeasurable g μ) {c : ℝ} (hc : 0 ≤ c) (k : ℕ) (hk : 1 ≤ k)
    (hb : ∀ ω, ‖f ω‖ ≤ c * g ω ^ k) {C : ℝ}
    (hC : eLpNorm g (ENNReal.ofReal (2 * k)) μ ≤ ENNReal.ofReal C) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal c * ENNReal.ofReal C ^ k := by
  refine (eLpNorm_mono_real hf hb).trans ?_
  have e : (fun ω => c * g ω ^ k) = c • fun ω => g ω ^ k := by funext ω; simp
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
  gcongr
  exact eLpNorm_pow_le hg0 hgm k hk hC

end Conv

end BlockBand.Transmission.PassiveCovariance
