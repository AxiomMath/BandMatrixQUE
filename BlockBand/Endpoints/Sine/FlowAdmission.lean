module

public import BlockBand.Endpoints.Sine.FlowAdmissionGirsanov
public import BlockBand.Endpoints.Sine.FlowAdmissionShifted

/-!
# Admission of the velocity error along the scalar pair flow

Statement (`flowAdmission : FlowAdmissionStatement`). Law: the exact physical law `model.law`.
Fixed first `0 < b < 1/2`, bulk `-2 < E < 2`, `T₀ > 0`, then `T, K` and a `C^∞` compactly
supported `χ ≥ 0` with `χ = 1` on `[-K, K]`; then one constant `C = C_{T,χ}` (also depending on
`b, E, T₀`); for every `τ ∈ (0, T₀]`, critical sequence `n/W → τ`, models and pair sequences:
`limsup_j E ∫_{-T}^T Σ_α χ(u_α(t))|v_α(t) - 1| dt ≤ C τ^{1/4}`
(`∀ ε > 0, ∀ᶠ j, · ≤ Cτ^{1/4} + ε`; the `limsup` form is `flowAdmission_limsup`). The
expectation is a lower integral (nonnegative integrand). The hypothesis `χ = 1` on `[-K, K]` is
not used (the bound holds for every such `χ ≥ 0`, `flowAdmission_general`). No density of a
selected eigenvalue and no inverse clock moment is used.

Proof. At each time `t`, `a = t/(𝒩ρ)`: the shifted law is `R_a · P` on the Gaussian coordinates
(`fa_lintegral_shift`); the weighted Cauchy–Schwarz inequality is used in its AM–GM form
`R F ≤ (λ/2) F + (2λ)⁻¹ R² F` (`fa_amgm`, `λ = τ^{-1/4}`; optimizing `λ` gives exactly the
Cauchy–Schwarz bound), `R_a² = e^{t²/(2cρ²)} R_{2a}` (`fa_lintegral_density_sq`), the shifted
observable is bounded uniformly (`fa_shifted_obs_le`), and the unshifted one is
`(∫χ) · E Σ_α w(u_α)|x_α - 1|` with the window `w = χ/∫χ` (`fa_obs_lintegral_eq`), controlled by
local mass flatness (`FaLocalMassFlatPair`). Tonelli in `(H, t)` and the uniformity in `|t| ≤ T`
integrate.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

/-- AM–GM form of the weighted Cauchy–Schwarz step: `xF ≤ (λ/2)F + (2λ)⁻¹x²F`. -/
theorem fa_amgm (x F : ℝ≥0∞) {l : ℝ} (hl : 0 < l) :
    x * F ≤ ENNReal.ofReal (l / 2) * F + ENNReal.ofReal (1 / (2 * l)) * (x ^ 2 * F) := by
  have key : x ≤ ENNReal.ofReal (l / 2) + ENNReal.ofReal (1 / (2 * l)) * x ^ 2 := by
    rcases eq_or_ne x ⊤ with rfl | hx
    · have : ENNReal.ofReal (1 / (2 * l)) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
      rw [ENNReal.top_pow two_ne_zero, ENNReal.mul_top this, add_top]
    · lift x to ℝ≥0 using hx
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (NNReal.coe_nonneg x),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h : l / 2 + 1 / (2 * l) * (x : ℝ) ^ 2 - x = (l - x) ^ 2 / (2 * l) := by
        field_simp; ring
      nlinarith [div_nonneg (sq_nonneg (l - (x : ℝ))) (by positivity : (0 : ℝ) ≤ 2 * l)]
  calc x * F ≤ (ENNReal.ofReal (l / 2) + ENNReal.ofReal (1 / (2 * l)) * x ^ 2) * F := by
        gcongr
    _ = _ := by rw [add_mul, mul_assoc]

section Pair

variable (p : Parameters) (i : ZMod p.n)

theorem fa_measurable_flowIntegrand (E : ℝ) {χ : ℝ → ℝ} (hχ : Continuous χ) :
    Measurable (Function.uncurry (fa_flowIntegrand p i E χ)) := by
  have hflow : Measurable fun x : p.SiteMatrix × ℝ => pairFlow p i x.1 E x.2 := by
    unfold pairFlow
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  exact (fa_measurable_obs p i E hχ).comp hflow

/-- The bound at one time. With `a = t/(𝒩ρ)`, for every `λ > 0`:
`E_t[F] ≤ (λ/2) E[F] + (2λ)⁻¹ e^{t²/(2cρ²)} E[F(H + 2aP_S)]`, `F = fa_obs`. -/
theorem fa_flow_time_le (model : p.GaussianRingModel) (E : ℝ)
    (hρ : 0 < Parameters.semicircleDensity E) {χ : ℝ → ℝ} (hχ : Continuous χ) {l : ℝ}
    (hl : 0 < l) (t : ℝ) :
    ∫⁻ H, fa_flowIntegrand p i E χ H t ∂(model.law : Measure p.SiteMatrix) ≤
      ENNReal.ofReal (l / 2) * ∫⁻ H, fa_obs p i E χ H ∂(model.law : Measure p.SiteMatrix) +
      ENNReal.ofReal (1 / (2 * l)) *
        (ENNReal.ofReal (Real.exp (t ^ 2 / (2 * p.c * Parameters.semicircleDensity E ^ 2))) *
          ∫⁻ H, fa_obs p i E χ
            (H + ((2 * (t / crossingScale p E) : ℝ) : ℂ) • pairProjector p i)
            ∂(model.law : Measure p.SiteMatrix)) := by
  set a := t / crossingScale p E with ha
  have hG := fa_measurable_obs p i E hχ
  have hGr := hG.comp p.measurable_gaussianReconstruction
  have h1 : ∫⁻ H, fa_flowIntegrand p i E χ H t ∂(model.law : Measure p.SiteMatrix) =
      ∫⁻ z, fa_density p i a z * fa_obs p i E χ (p.gaussianReconstruction z)
        ∂fa_coordLaw p :=
    fa_lintegral_shift p i model a hG
  have hK : fa_densitySqConst p i a =
      ENNReal.ofReal (Real.exp (t ^ 2 / (2 * p.c * Parameters.semicircleDensity E ^ 2))) := by
    rw [fa_densitySqConst_eq]
    congr 2
    have hW : (0 : ℝ) < p.W := Nat.cast_pos.mpr p.W_pos
    rw [ha, crossingScale]
    field_simp
  rw [h1]
  calc ∫⁻ z, fa_density p i a z * fa_obs p i E χ (p.gaussianReconstruction z) ∂fa_coordLaw p
      ≤ ∫⁻ z, (ENNReal.ofReal (l / 2) * fa_obs p i E χ (p.gaussianReconstruction z) +
          ENNReal.ofReal (1 / (2 * l)) *
            (fa_density p i a z ^ 2 * fa_obs p i E χ (p.gaussianReconstruction z)))
          ∂fa_coordLaw p := lintegral_mono fun z => fa_amgm _ _ hl
    _ = ENNReal.ofReal (l / 2) * ∫⁻ z, fa_obs p i E χ (p.gaussianReconstruction z)
            ∂fa_coordLaw p +
          ENNReal.ofReal (1 / (2 * l)) * ∫⁻ z, fa_density p i a z ^ 2 *
            fa_obs p i E χ (p.gaussianReconstruction z) ∂fa_coordLaw p := by
        have hGr' : Measurable fun z => fa_obs p i E χ (p.gaussianReconstruction z) := hGr
        have hm1 : Measurable fun z =>
            ENNReal.ofReal (l / 2) * fa_obs p i E χ (p.gaussianReconstruction z) :=
          hGr'.const_mul _
        have hm2 : Measurable fun z =>
            fa_density p i a z ^ 2 * fa_obs p i E χ (p.gaussianReconstruction z) :=
          ((fa_measurable_density p i a).pow_const 2).mul hGr'
        rw [lintegral_add_left hm1, lintegral_const_mul _ hGr', lintegral_const_mul _ hm2]
    _ = _ := by
        rw [fa_lintegral_reconstruction p model hG, fa_lintegral_density_sq p i model a hG, hK]

/-- Finite-`W` integrated bound. With `B` the uniform shifted bound of `fa_shifted_obs_le`:
`E ∫_{-T}^T Σ_α χ(u_α(t))|v_α(t) - 1| dt ≤ 2|T| ((λ/2) E[F] + (2λ)⁻¹ e^{T²/(2cρ²)} B)`. -/
theorem fa_velocityError_le (model : p.GaussianRingModel) (E T : ℝ)
    (hρ : 0 < Parameters.semicircleDensity E) {χ : ℝ → ℝ} (hχ : Continuous χ) {l : ℝ}
    (hl : 0 < l) {B : ℝ}
    (hB : ∀ a : ℝ, ∫⁻ H, fa_obs p i E χ (H + (a : ℂ) • pairProjector p i)
        ∂(model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal B) :
    fa_velocityError p model i E T χ ≤ ENNReal.ofReal (2 * |T|) *
      (ENNReal.ofReal (l / 2) * ∫⁻ H, fa_obs p i E χ H ∂(model.law : Measure p.SiteMatrix) +
        ENNReal.ofReal (1 / (2 * l)) *
          (ENNReal.ofReal (Real.exp (T ^ 2 / (2 * p.c * Parameters.semicircleDensity E ^ 2))) *
            ENNReal.ofReal B)) := by
  unfold fa_velocityError
  rw [lintegral_lintegral_swap (fa_measurable_flowIntegrand p i E hχ).aemeasurable]
  set Bd := ENNReal.ofReal (l / 2) * ∫⁻ H, fa_obs p i E χ H ∂(model.law : Measure p.SiteMatrix) +
    ENNReal.ofReal (1 / (2 * l)) *
      (ENNReal.ofReal (Real.exp (T ^ 2 / (2 * p.c * Parameters.semicircleDensity E ^ 2))) *
        ENNReal.ofReal B) with hBd
  have hc : 0 < p.c := p.c_pos
  calc ∫⁻ t in Set.Icc (-T) T, ∫⁻ H, fa_flowIntegrand p i E χ H t
        ∂(model.law : Measure p.SiteMatrix)
      ≤ ∫⁻ _t in Set.Icc (-T) T, Bd := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        refine (fa_flow_time_le p i model E hρ hχ hl t).trans ?_
        rw [hBd]
        gcongr _ + _ * (?_ * ?_)
        · refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          exact div_le_div_of_nonneg_right (sq_le_sq' ht.1 ht.2) (by positivity)
        · exact hB _
    _ = Bd * volume (Set.Icc (-T) T) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (2 * |T|) * Bd := by
        rw [Real.volume_Icc, mul_comm]
        gcongr
        rw [sub_neg_eq_add, ← two_mul]
        exact mul_le_mul_of_nonneg_left (le_abs_self T) (by norm_num)

/-- The unshifted observable through the window `w = χ/∫χ`. For continuous compactly supported
`χ ≥ 0` with `m = ∫χ > 0`: `E[F] = m · E Σ_α w(u_α)|x_α - 1|`. -/
theorem fa_obs_lintegral_eq (model : p.GaussianRingModel) (E : ℝ) {χ : ℝ → ℝ}
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) {m : ℝ}
    (hm : 0 < m) :
    ∫⁻ H, fa_obs p i E χ H ∂(model.law : Measure p.SiteMatrix) =
      ENNReal.ofReal (m * fa_pairFlatness p model E (fun x => m⁻¹ * χ x) i) := by
  obtain ⟨M, hM⟩ := hχc.bounded_above_of_compact_support hχs
  set g : p.SiteMatrix → ℝ := fun H => ∑ α : Fin p.N,
    χ (microCoord p E (physicalOrderedEigenvalue p H α)) *
      |(p.n : ℝ) / 2 * pairMass p i α H - 1|
  have hg0 : ∀ H, 0 ≤ g H := fun H =>
    Finset.sum_nonneg fun α _ => mul_nonneg (hχ0 _) (abs_nonneg _)
  have hgm : Measurable g := by
    refine Finset.measurable_sum _ fun α _ => ?_
    exact ((hχc.measurable.comp ((fa_measurable_microCoord p E).comp
      (measurable_physicalOrderedEigenvalue p α))).mul
      ((((fa_measurable_pairMass p i α).const_mul _).sub_const 1).abs))
  have hgi : Integrable g (model.law : Measure p.SiteMatrix) := by
    refine Integrable.of_bound hgm.aestronglyMeasurable ((p.N : ℝ) * (M * (p.n + 1))) ?_
    filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH
    rw [Real.norm_of_nonneg (hg0 H)]
    calc g H ≤ ∑ _α : Fin p.N, M * (p.n + 1) := by
          refine Finset.sum_le_sum fun α _ => ?_
          have hk : ∀ k, physicalOrderedBlockMass p H α k ≤ 1 := fun k => by
            rw [← hH α]
            exact Finset.single_le_sum (fun k _ => physicalOrderedBlockMass_nonneg p H α k)
              (Finset.mem_univ k)
          have hq : pairMass p i α H ≤ 2 := by
            unfold pairMass; linarith [hk i, hk (i + 1)]
          have hq0 := fa_pairMass_nonneg p i α H
          have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
          have habs : |(p.n : ℝ) / 2 * pairMass p i α H - 1| ≤ p.n + 1 := by
            rw [abs_le]; constructor <;> nlinarith
          have hχM := (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸
            hM (microCoord p E (physicalOrderedEigenvalue p H α)))
          exact mul_le_mul hχM habs (abs_nonneg _) ((norm_nonneg _).trans (hM 0))
      _ = (p.N : ℝ) * (M * (p.n + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hobs : ∀ H, fa_obs p i E χ H = ENNReal.ofReal (g H) := fun H => by
    unfold fa_obs
    rw [ENNReal.ofReal_sum_of_nonneg fun α _ => mul_nonneg (hχ0 _) (abs_nonneg _)]
  simp_rw [hobs]
  rw [← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0)]
  congr 1
  unfold fa_pairFlatness
  rw [← integral_const_mul]
  congr 1
  funext H
  simp only [g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  field_simp

end Pair

/-- Flow admission for every smooth compactly supported `χ ≥ 0` (the plateau condition `χ = 1`
on `[-K, K]` is not needed). Same quantifiers as `FlowAdmissionStatement` without `K`. -/
theorem flowAdmission_general (hPalm : ExactPalmContract) (hCo : CoareaContract)
    (hShift : FaShiftedMassPalm) (hCount : PhysicalBlockConditionalCount)
    (hLMF : FaLocalMassFlatPair) :
    ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 → ∀ T₀ : ℝ, 0 < T₀ →
    ∀ (T : ℝ) (χ : ℝ → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x) →
    ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T₀ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel)
      (i : ∀ j, ZMod (s.parameters b hb hb' j).n),
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        fa_velocityError (s.parameters b hb hb' j) (R j) (i j) E T χ ≤
          ENNReal.ofReal (C * τ ^ (1 / 4 : ℝ) + ε) := by
  intro b hb hb' E hE1 hE2 T₀ hT₀ T χ hχ hχs hχ0
  have hχc : Continuous χ := hχ.continuous
  have hint : Integrable χ := hχc.integrable_of_hasCompactSupport hχs
  set m := ∫ x, χ x with hm_def
  by_cases hm : m = 0
  · -- `χ ≡ 0`
    have hz : χ = 0 := by
      have h0 : χ =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hχ0 hint).mp hm
      exact (hχc.ae_eq_iff_eq volume continuous_const).mp h0
    refine ⟨0, fun τ _ _ s R i ε _ => Eventually.of_forall fun j => ?_⟩
    simp [fa_velocityError, fa_flowIntegrand, fa_obs, hz]
  have hmpos : 0 < m := lt_of_le_of_ne (integral_nonneg hχ0) (Ne.symm hm)
  set w : ℝ → ℝ := fun x => m⁻¹ * χ x with hw_def
  have hwsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := contDiff_const.mul hχ
  have hwwin : IsWindow w := by
    refine ⟨continuous_const.mul hχc, hχs.mul_left, fun x => ?_, ?_⟩
    · exact mul_nonneg (inv_nonneg.mpr hmpos.le) (hχ0 x)
    · simp only [w]
      rw [integral_const_mul, ← hm_def, inv_mul_cancel₀ hm]
  obtain ⟨Cl, hCl⟩ := hLMF b hb hb' E hE1 hE2 T₀ hT₀ w hwsm hwwin
  obtain ⟨B, hB0, hB⟩ :=
    fa_shifted_obs_le hPalm hCo hShift hCount b hb hb' E hE1 hE2 hχc hχs hχ0
  have hρ := fa_rho_pos hE1 hE2
  set ρ := Parameters.semicircleDensity E with hρ_def
  set Kt := Real.exp (T ^ 2 / (2 * (1 - 2 * b) * ρ ^ 2)) with hKt
  have hKt0 : 0 ≤ Kt := (Real.exp_pos _).le
  set Cp := max Cl 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  refine ⟨|T| * (m * Cp + Kt * B), fun τ hτ hτ0 s R i ε hε => ?_⟩
  set q := τ ^ (1 / 4 : ℝ) with hq_def
  have hq : 0 < q := Real.rpow_pos_of_pos hτ _
  have hsq : Real.sqrt τ = q ^ 2 := by
    rw [hq_def, ← Real.rpow_natCast, ← Real.rpow_mul hτ.le, Real.sqrt_eq_rpow]
    norm_num
  have hTm : 0 ≤ |T| * m := mul_nonneg (abs_nonneg T) hmpos.le
  set ε' := ε * q / (|T| * m + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  filter_upwards [hCl τ hτ hτ0 s R i ε' hε'0] with j hj
  set p := s.parameters b hb hb' j
  have hp : p.b = b := rfl
  have hpc : p.c = 1 - 2 * b := by rw [Parameters.c, hp]
  have hl : 0 < 1 / q := one_div_pos.mpr hq
  have h1 := fa_velocityError_le p (i j) (R j) E T hρ hχc hl (hB p hp (R j) (i j))
  rw [fa_obs_lintegral_eq p (i j) (R j) E hχc hχs hχ0 hmpos, hpc] at h1
  refine h1.trans ?_
  rw [hsq] at hj
  have hA : m * fa_pairFlatness p (R j) E w (i j) ≤ m * (Cp * q ^ 2 + ε') := by
    gcongr
    exact hj.trans (by gcongr; exact le_max_left _ _)
  calc ENNReal.ofReal (2 * |T|) * (ENNReal.ofReal (1 / q / 2) *
          ENNReal.ofReal (m * fa_pairFlatness p (R j) E w (i j)) +
        ENNReal.ofReal (1 / (2 * (1 / q))) * (ENNReal.ofReal Kt * ENNReal.ofReal B))
      ≤ ENNReal.ofReal (2 * |T|) * (ENNReal.ofReal (1 / q / 2) *
          ENNReal.ofReal (m * (Cp * q ^ 2 + ε')) +
        ENNReal.ofReal (1 / (2 * (1 / q))) * (ENNReal.ofReal Kt * ENNReal.ofReal B)) := by
        gcongr
    _ = ENNReal.ofReal (2 * |T| * (1 / q / 2 * (m * (Cp * q ^ 2 + ε')) +
          1 / (2 * (1 / q)) * (Kt * B))) := by
        rw [← ENNReal.ofReal_mul hKt0, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (|T| * (m * Cp + Kt * B) * q + ε) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hsplit : 2 * |T| * (1 / q / 2 * (m * (Cp * q ^ 2 + ε')) +
            1 / (2 * (1 / q)) * (Kt * B)) =
            |T| * (m * Cp + Kt * B) * q + (|T| * m) * ε' / q := by
          field_simp; ring
        have hsmall : (|T| * m) * ε' / q ≤ ε := by
          rw [hε', div_le_iff₀ hq]
          rw [show |T| * m * (ε * q / (|T| * m + 1)) = ε * q * (|T| * m / (|T| * m + 1)) by
            field_simp]
          have : |T| * m / (|T| * m + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith [mul_pos hε hq]
        rw [hsplit]; linarith

/-- **Flow admission** (`FlowAdmissionStatement`), from `ExactPalmContract`, `CoareaContract`,
`PhysicalBlockConditionalCount`, the pair clause `FaLocalMassFlatPair` of the local mass flatness
theorem and the shifted mass-Palm identity `FaShiftedMassPalm` (proved from `CoareaContract` as
`faShiftedMassPalm_holds`). -/
theorem flowAdmission (hPalm : ExactPalmContract) (hCo : CoareaContract)
    (hShift : FaShiftedMassPalm) (hCount : PhysicalBlockConditionalCount)
    (hLMF : FaLocalMassFlatPair) : FlowAdmissionStatement := by
  intro b hb hb' E hE1 hE2 T₀ hT₀ T _K χ hχ hχs hχ0 _hK
  exact flowAdmission_general hPalm hCo hShift hCount hLMF b hb hb' E hE1 hE2 T₀ hT₀ T χ hχ hχs
    hχ0

/-- `limsup` form of flow admission:
`limsup_j E ∫_{-T}^T Σ_α χ(u_α(t))|v_α(t) - 1| dt ≤ C τ^{1/4}` in `ℝ≥0∞`. -/
theorem flowAdmission_limsup (hPalm : ExactPalmContract) (hCo : CoareaContract)
    (hShift : FaShiftedMassPalm) (hCount : PhysicalBlockConditionalCount)
    (hLMF : FaLocalMassFlatPair) :
    ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 → ∀ T₀ : ℝ, 0 < T₀ →
    ∀ (T K : ℝ) (χ : ℝ → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x) → (∀ x ∈ Set.Icc (-K) K, χ x = 1) →
    ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T₀ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel)
      (i : ∀ j, ZMod (s.parameters b hb hb' j).n),
        limsup (fun j => fa_velocityError (s.parameters b hb hb' j) (R j) (i j) E T χ) atTop ≤
          ENNReal.ofReal (C * τ ^ (1 / 4 : ℝ)) := by
  intro b hb hb' E hE1 hE2 T₀ hT₀ T K χ hχ hχs hχ0 hK
  obtain ⟨C, hC⟩ := flowAdmission hPalm hCo hShift hCount hLMF b hb hb' E hE1 hE2 T₀ hT₀ T K χ
    hχ hχs hχ0 hK
  refine ⟨C, fun τ hτ hτ0 s R i => ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_⟩
  refine limsup_le_of_le (h := (hC τ hτ hτ0 s R i δ hδ).mono fun j hj => hj.trans ?_)
  refine (ENNReal.ofReal_add_le).trans_eq ?_
  rw [ENNReal.ofReal_coe_nnreal]

end BlockBand.Endpoints
