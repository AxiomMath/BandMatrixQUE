module

public import BlockBand.SourceProcess.PhysApprox.B3BirthPTrace
public import BlockBand.SourceProcess.RawTag.FrameMoments
public import BlockBand.SourceProcess.ComplexSourceLaw.GaussianForms
public import BlockBand.Transmission.EnergyUniform.Holds

/-!
# The unclosed cross estimate `ComplexBirthKFreshCross`

One step after a birth at `j` (`n_s ≤ j < ⌊WT⌋`), an unclosed entry `𝒦_{aa'}`, `a ≠ a'`, with a
newborn index is handled as follows (eventually in `W`).
* **New/new does not occur**: `τ` is injective, so eventually `⌊Wτ_a⌋ ≠ ⌊Wτ_{a'}⌋`
  (`BirthP.eventually_floor_ne`).
* **New/unborn**: the other column is still `0` (`Birth.complexSourceK_unborn_row/col`).
* **New/old**: by the proved `RawTag.rawBirth_holds`, `𝒦_{a,new} = √(m_am)·ξ*(1 + ΔR)W^{-1/2}g`
  and `𝒦_{new,a'} = √(mm_{a'})·W^{-1/2}g*(1 + RΔ)ν` with the newborn probe `g` independent of
  the near frame `ξ = nearL` (resp. `ν = nearR`). The circular average over `g` gives
  `E_g|·| ≤ W^{-1/2}‖(1 + ΔR)ᴴξ‖` (`BirthP.lintegral_bilinear_unitVec_left/right_le`), and
  `RawTag.momBd_stepDelta`, `RawTag.momBd_frame` give
  `E|𝒦| ≤ √(m_am_{a'})·W^{-1/2}(1 + eC_Δ)A` (`BirthP.lintegral_kc_cross_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.FullSource BlockBand.SourceProcess.RawTag
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ClosedPath
open scoped ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

namespace BirthP

variable {W : ℕ}

/-!
## Circular averages of linear forms
-/

/-- Cauchy–Schwarz on a probability space: `∫ f ≤ (∫ f²)^{1/2}`. -/
theorem lintegral_le_sqrt_of_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ a, f a ^ 2 ∂μ ≤ ENNReal.ofReal c) : ∫⁻ a, f a ∂μ ≤ ENNReal.ofReal (Real.sqrt c) := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at hH
  refine hH.trans ?_
  have h2 : ∫⁻ a, f a ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal c := by
    simpa only [ENNReal.rpow_two] using h
  calc (∫⁻ a, f a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal c) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt c) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hc (by norm_num), Real.sqrt_eq_rpow]

theorem enorm_sq_eq (z : ℂ) : ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- `E|Σ c_a g_a| ≤ (Σ|c_a|²)^{1/2}`. -/
theorem lintegral_lin_le (c : Fin W → ℂ) :
    ∫⁻ g, ‖∑ a, c a * g a‖ₑ ∂circularVectorLaw (Fin W) ≤
      ENNReal.ofReal (Real.sqrt (∑ a, ‖c a‖ ^ 2)) := by
  refine lintegral_le_sqrt_of_sq ?_ (Finset.sum_nonneg fun _ _ => by positivity) (le_of_eq ?_)
  · exact (Finset.measurable_sum _ fun a _ =>
      measurable_const.mul (measurable_pi_apply a)).enorm.aemeasurable
  · simp_rw [enorm_sq_eq]
    exact lintegral_norm_sq_lin c

/-- `E|Σ c_a ḡ_a| ≤ (Σ|c_a|²)^{1/2}`. -/
theorem lintegral_conj_lin_le (c : Fin W → ℂ) :
    ∫⁻ g, ‖∑ a, c a * conj (g a)‖ₑ ∂circularVectorLaw (Fin W) ≤
      ENNReal.ofReal (Real.sqrt (∑ a, ‖c a‖ ^ 2)) := by
  refine lintegral_le_sqrt_of_sq ?_ (Finset.sum_nonneg fun _ _ => by positivity) (le_of_eq ?_)
  · exact (Finset.measurable_sum _ fun a _ => measurable_const.mul
      (Complex.continuous_conj.measurable.comp (measurable_pi_apply a))).enorm.aemeasurable
  · simp_rw [enorm_sq_eq]
    exact lintegral_norm_sq_conj_lin c

theorem sqrt_sum_scaled (w : Fin W → ℂ) :
    Real.sqrt (∑ a, ‖((Real.sqrt (1 / W) : ℝ) : ℂ) * w a‖ ^ 2) =
      Real.sqrt (1 / W) * vecNorm w := by
  have e : ∑ a, ‖((Real.sqrt (1 / W) : ℝ) : ℂ) * w a‖ ^ 2 =
      Real.sqrt (1 / W) ^ 2 * ∑ a, ‖w a‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.sqrt_nonneg _), vecNorm]

/-- **The circular average of a form with the probe on the left**:
`E_g|(W^{-1/2}g)*Mv| ≤ W^{-1/2}‖Mv‖`. -/
theorem lintegral_bilinear_unitVec_left_le (M : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    ∫⁻ g, ‖bilinear (unitVec W g) M v‖ₑ ∂circularVectorLaw (Fin W) ≤
      ENNReal.ofReal (Real.sqrt (1 / W) * vecNorm (M *ᵥ v)) := by
  have e : ∀ g : Fin W → ℂ, bilinear (unitVec W g) M v =
      ∑ a, (((Real.sqrt (1 / W) : ℝ) : ℂ) * (M *ᵥ v) a) * conj (g a) := by
    intro g
    simp only [bilinear, dotProduct, unitVec, Pi.star_apply, star_mul', Complex.star_def,
      Complex.conj_ofReal]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp_rw [e]
  refine (lintegral_conj_lin_le _).trans (le_of_eq ?_)
  rw [sqrt_sum_scaled]

/-- **The circular average of a form with the probe on the right**:
`E_g|u*M(W^{-1/2}g)| ≤ W^{-1/2}‖Mᴴu‖`. -/
theorem lintegral_bilinear_unitVec_right_le (M : Matrix (Fin W) (Fin W) ℂ) (u : Fin W → ℂ) :
    ∫⁻ g, ‖bilinear u M (unitVec W g)‖ₑ ∂circularVectorLaw (Fin W) ≤
      ENNReal.ofReal (Real.sqrt (1 / W) * vecNorm (Mᴴ *ᵥ u)) := by
  have e : ∀ g : Fin W → ℂ, bilinear u M (unitVec W g) =
      ∑ a, (((Real.sqrt (1 / W) : ℝ) : ℂ) * star ((Mᴴ *ᵥ u) a)) * g a := by
    intro g
    have hs : star u ᵥ* M = star (Mᴴ *ᵥ u) := by
      rw [star_mulVec, conjTranspose_conjTranspose]
    rw [bilinear, dotProduct_mulVec, hs]
    simp only [dotProduct, unitVec, Pi.star_apply]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp_rw [e]
  refine (lintegral_lin_le _).trans (le_of_eq ?_)
  have hn : ∀ a, ‖((Real.sqrt (1 / W) : ℝ) : ℂ) * star ((Mᴴ *ᵥ u) a)‖ =
      ‖((Real.sqrt (1 / W) : ℝ) : ℂ) * (Mᴴ *ᵥ u) a‖ := fun a => by
    rw [norm_mul, norm_mul, norm_star]
  simp_rw [hn]
  rw [sqrt_sum_scaled]

/-!
## Tonelli over the probes
-/

theorem measurable_unitVec : Measurable (unitVec W) := by
  refine Measurable.of_eval fun a => ?_
  simp only [unitVec]
  exact measurable_const.mul (measurable_pi_apply a)

theorem measurable_bilinear_vec {α : Type*} [MeasurableSpace α] (M : Matrix (Fin W) (Fin W) ℂ)
    {u v : α → Fin W → ℂ} (hu : Measurable u) (hv : Measurable v) :
    Measurable fun a => bilinear (u a) M (v a) := by
  simp only [bilinear, dotProduct, mulVec, Pi.star_apply]
  exact Finset.measurable_sum _ fun x _ =>
    (Complex.continuous_conj.measurable.comp ((measurable_pi_apply x).comp hu)).mul
      (Finset.measurable_sum _ fun y _ => measurable_const.mul ((measurable_pi_apply y).comp hv))

/-- **Tonelli over two probes**: an integrand bounded, a.s. in the path, by a function `Φ` of the
two probes `g_i, g_k` (`i ≠ k`), whose average over `g_i` is at most `Ψ(ω, g_k)`. -/
theorem lintegral_probed_pair_le {np : ℕ} {b : ℝ} {i k : Fin np} (hik : i ≠ k)
    {f : ProbedPath W np → ℝ≥0∞} {Φ : GrowthPath W → (Fin W → ℂ) → (Fin W → ℂ) → ℝ≥0∞}
    {Ψ : GrowthPath W × (Fin W → ℂ) → ℝ≥0∞}
    (hf : ∀ᵐ ω ∂growthPathLaw W b, ∀ G, f (ω, G) ≤ Φ ω (G i) (G k))
    (hΦ : ∀ ω, Measurable fun p : (Fin W → ℂ) × (Fin W → ℂ) => Φ ω p.1 p.2)
    (hin : ∀ᵐ ω ∂growthPathLaw W b, ∀ h, ∫⁻ g, Φ ω g h ∂circularVectorLaw (Fin W) ≤ Ψ (ω, h))
    (hΨ : AEMeasurable Ψ ((growthPathLaw W b).prod (circularVectorLaw (Fin W)))) :
    ∫⁻ x, f x ∂probedPathLaw W np b ≤
      ∫⁻ w, Ψ w ∂(growthPathLaw W b).prod (circularVectorLaw (Fin W)) := by
  have hpair : Measurable fun G : Fin np → Fin W → ℂ => (G i, G k) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply k)
  rw [lintegral_prod _ hΨ]
  refine (lintegral_prod_le _).trans (lintegral_mono_ae ?_)
  filter_upwards [hf, hin] with ω hfω hinω
  calc ∫⁻ G, f (ω, G) ∂Measure.pi (fun _ : Fin np => circularVectorLaw (Fin W))
      ≤ ∫⁻ G, Φ ω (G i) (G k) ∂Measure.pi (fun _ : Fin np => circularVectorLaw (Fin W)) :=
        lintegral_mono fun G => hfω G
    _ = ∫⁻ p, Φ ω p.1 p.2 ∂(circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W)) := by
        rw [← pi_map_pair (circularVectorLaw (Fin W)) hik, lintegral_map (hΦ ω) hpair]
    _ = ∫⁻ h, ∫⁻ g, Φ ω g h ∂circularVectorLaw (Fin W) ∂circularVectorLaw (Fin W) :=
        lintegral_prod_symm _ (hΦ ω).aemeasurable
    _ ≤ ∫⁻ h, Ψ (ω, h) ∂circularVectorLaw (Fin W) := lintegral_mono hinω

/-!
## The cross entries as raw forms
-/

/-- **A `𝒦` entry of two born tags is a raw form** at their birth indices. -/
theorem kc_eq_rawForm (b E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (hm : ∀ i, 0 ≤ m i) {n : ℕ}
    {i k : Fin np} (hi : ⌊(W : ℝ) * τ i⌋₊ < n) (hk : ⌊(W : ℝ) * τ k⌋₊ < n)
    (x : ProbedPath W np) :
    complexSourceK b E W n τ m x i k = ((Real.sqrt (m i) * Real.sqrt (m k) : ℝ) : ℂ) *
      rawForm b E W n ⌊(W : ℝ) * τ i⌋₊ ⌊(W : ℝ) * τ k⌋₊ x.1 (x.2 i) (x.2 k) := by
  rw [complexSourceK_apply, probeColumn_eq_tagVector n τ m _ i hi,
    probeColumn_eq_tagVector n τ m _ k hk, ComplexSourceLaw.tagForm,
    tagForm_eq_rawForm b E n _ _ (hm i) (hm k)]
  have h1 : n - 1 - (n - 1 - ⌊(W : ℝ) * τ i⌋₊) = ⌊(W : ℝ) * τ i⌋₊ := by omega
  have h2 : n - 1 - (n - 1 - ⌊(W : ℝ) * τ k⌋₊) = ⌊(W : ℝ) * τ k⌋₊ := by omega
  simp only [h1, h2]

/-- Distinct positive times have distinct birth steps eventually. -/
theorem eventually_floor_ne {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t') (hne : t ≠ t') :
    ∀ᶠ W : ℕ in atTop, ⌊(W : ℝ) * t⌋₊ ≠ ⌊(W : ℝ) * t'⌋₊ := by
  have hd : 0 < |t - t'| := abs_pos.mpr (sub_ne_zero.mpr hne)
  filter_upwards [(tendsto_natCast_atTop_atTop.atTop_mul_const hd).eventually_ge_atTop 1]
    with W hW heq
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have a1 := Nat.floor_le (mul_nonneg hW0 ht.le)
  have a2 := Nat.lt_floor_add_one ((W : ℝ) * t)
  have a3 := Nat.floor_le (mul_nonneg hW0 ht'.le)
  have a4 := Nat.lt_floor_add_one ((W : ℝ) * t')
  rw [heq] at a1 a2
  have : |(W : ℝ) * t - W * t'| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  rw [← mul_sub, abs_mul, abs_of_nonneg hW0] at this
  linarith

/-- **The old/new and new/old cross entries in `L¹`**: one step after the birth `j ≥ 1` of `i`,
with `k` born at `β < j`, `E|𝒦_{ik}| + E|𝒦_{ki}| ≤ 2√(m_im_k)·W^{-1/2}·Cst` (each term),
given `‖R_j‖ ≤ e` a.s. and second moments of `1 + e‖Δ_j‖` and of the near frames. -/
theorem lintegral_kc_cross_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) {np : ℕ} (τ m : Fin np → ℝ) (hm : ∀ i, 0 ≤ m i) {i k : Fin np}
    (hik : i ≠ k) {j : ℕ} (hj : 1 ≤ j) (hi : ⌊(W : ℝ) * τ i⌋₊ = j) (hk : ⌊(W : ℝ) * τ k⌋₊ < j)
    {e C : ℝ} (he : 0 ≤ e) (hC : 0 ≤ C)
    (hR : ∀ᵐ ω ∂growthPathLaw W b, ‖stepR b E W j ω‖ ≤ e)
    (hML : MomBd ((growthPathLaw W b).prod (circularVectorLaw (Fin W))) (fun w =>
      (1 + e * ‖stepDelta b E W j w.1‖) * vecNorm (nearL b E W j ⌊(W : ℝ) * τ k⌋₊ w.1 w.2)) 1 C)
    (hMR : MomBd ((growthPathLaw W b).prod (circularVectorLaw (Fin W))) (fun w =>
      (1 + e * ‖stepDelta b E W j w.1‖) * vecNorm (nearR b E W j ⌊(W : ℝ) * τ k⌋₊ w.1 w.2)) 1 C) :
    ∫⁻ x, ‖complexSourceK b E W (j + 1) τ m x i k‖ₑ ∂probedPathLaw W np b ≤
        ENNReal.ofReal (Real.sqrt (m i) * Real.sqrt (m k) * Real.sqrt (1 / W) * C) ∧
      ∫⁻ x, ‖complexSourceK b E W (j + 1) τ m x k i‖ₑ ∂probedPathLaw W np b ≤
        ENNReal.ofReal (Real.sqrt (m i) * Real.sqrt (m k) * Real.sqrt (1 / W) * C) := by
  set β := ⌊(W : ℝ) * τ k⌋₊ with hβ
  set c := Real.sqrt (m i) * Real.sqrt (m k) with hc
  set s := Real.sqrt (1 / W) with hs
  have hc0 : 0 ≤ c := by positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hcs : 0 ≤ c * s := mul_nonneg hc0 hs0
  have hi' : ⌊(W : ℝ) * τ i⌋₊ < j + 1 := by omega
  have hk' : ⌊(W : ℝ) * τ k⌋₊ < j + 1 := by omega
  have hβj : β < j := hk
  have hbirth := rawBirth_holds b E hb0 hb hE1 hE2 W hW
  have hnn : ∀ (F : GrowthPath W × (Fin W → ℂ) → ℝ), (∀ w, 0 ≤ F w) →
      MomBd ((growthPathLaw W b).prod (circularVectorLaw (Fin W))) F 1 C →
      ∫⁻ w, ENNReal.ofReal (c * s * F w) ∂(growthPathLaw W b).prod (circularVectorLaw (Fin W)) ≤
        ENNReal.ofReal (c * s * C) := by
    intro F hF0 hF
    have hI := lintegral_rpow_le_of_momBd hF one_pos hC
    simp only [Real.rpow_one] at hI
    simp_rw [ENNReal.ofReal_mul hcs]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul_right (le_trans (le_of_eq (lintegral_congr fun w => ?_)) hI) _
    rw [abs_of_nonneg (hF0 w)]
  constructor
  · -- `i` new on the left: `𝒦_{ik} = c·(W^{-1/2}g_i)*(1 + RΔ)ν_k`
    set M : GrowthPath W → Matrix (Fin W) (Fin W) ℂ :=
      fun ω => 1 + stepR b E W j ω * stepDelta b E W j ω
    set F : GrowthPath W × (Fin W → ℂ) → ℝ :=
      fun w => (1 + e * ‖stepDelta b E W j w.1‖) * vecNorm (nearR b E W j β w.1 w.2)
    have hF0 : ∀ w, 0 ≤ F w := fun w => by
      have := vecNorm_nonneg (nearR b E W j β w.1 w.2)
      positivity
    refine (lintegral_probed_pair_le (Φ := fun ω g h => ENNReal.ofReal c *
        ‖bilinear (unitVec W g) (M ω) (nearR b E W j β ω h)‖ₑ)
      (Ψ := fun w => ENNReal.ofReal (c * s * F w)) hik ?_ ?_ ?_
      (hMR.1.aemeasurable.const_mul _).ennreal_ofReal).trans (hnn F hF0 hMR)
    · filter_upwards [hbirth] with ω hω G
      rw [kc_eq_rawForm b E τ m hm hi' hk', hi, (hω j hj).2.1 β hβj, enorm_mul,
        ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hc0]
    · intro ω
      exact measurable_const.mul (measurable_bilinear_vec _ (measurable_unitVec.comp
        measurable_fst) (measurable_nearR b E j β measurable_const measurable_snd)).enorm
    · filter_upwards [hR] with ω hRω h
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine (mul_le_mul_right (lintegral_bilinear_unitVec_left_le _ _) _).trans ?_
      rw [← ENNReal.ofReal_mul hc0]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := vecNorm_mulVec_le (M ω) (nearR b E W j β ω h)
      have h2 := norm_one_add_mul_le' (M := stepDelta b E W j ω) hRω
      have h3 := vecNorm_nonneg (nearR b E W j β ω h)
      have h4 : vecNorm (M ω *ᵥ nearR b E W j β ω h) ≤ F (ω, h) := by
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ h3)
        simp only [M]
        linarith [mul_comm e ‖stepDelta b E W j ω‖]
      calc c * (s * vecNorm (M ω *ᵥ nearR b E W j β ω h)) ≤ c * (s * F (ω, h)) := by gcongr
        _ = c * s * F (ω, h) := by ring
  · -- `i` new on the right: `𝒦_{ki} = c·ξ_k*(1 + ΔR)(W^{-1/2}g_i)`
    set M : GrowthPath W → Matrix (Fin W) (Fin W) ℂ :=
      fun ω => 1 + stepDelta b E W j ω * stepR b E W j ω
    set F : GrowthPath W × (Fin W → ℂ) → ℝ :=
      fun w => (1 + e * ‖stepDelta b E W j w.1‖) * vecNorm (nearL b E W j β w.1 w.2)
    have hF0 : ∀ w, 0 ≤ F w := fun w => by
      have := vecNorm_nonneg (nearL b E W j β w.1 w.2)
      positivity
    refine (lintegral_probed_pair_le (Φ := fun ω g h => ENNReal.ofReal c *
        ‖bilinear (nearL b E W j β ω h) (M ω) (unitVec W g)‖ₑ)
      (Ψ := fun w => ENNReal.ofReal (c * s * F w)) hik ?_ ?_ ?_
      (hML.1.aemeasurable.const_mul _).ennreal_ofReal).trans (hnn F hF0 hML)
    · filter_upwards [hbirth] with ω hω G
      rw [kc_eq_rawForm b E τ m hm hk' hi', hi, (hω j hj).1 β hβj, enorm_mul,
        ← ofReal_norm, Complex.norm_real, show Real.sqrt (m k) * Real.sqrt (m i) = c by
          rw [hc, mul_comm], Real.norm_of_nonneg hc0]
    · intro ω
      exact measurable_const.mul (measurable_bilinear_vec _
        (measurable_nearL b E j β measurable_const measurable_snd)
        (measurable_unitVec.comp measurable_fst)).enorm
    · filter_upwards [hR] with ω hRω h
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine (mul_le_mul_right (lintegral_bilinear_unitVec_right_le _ _) _).trans ?_
      rw [← ENNReal.ofReal_mul hc0]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := vecNorm_mulVec_le (M ω)ᴴ (nearL b E W j β ω h)
      have h2 := norm_one_add_mul_le (M := stepDelta b E W j ω) hRω
      have h3 := vecNorm_nonneg (nearL b E W j β ω h)
      have h4 : vecNorm ((M ω)ᴴ *ᵥ nearL b E W j β ω h) ≤ F (ω, h) := by
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ h3)
        rw [Matrix.l2_opNorm_conjTranspose]
        simp only [M]
        linarith [mul_comm e ‖stepDelta b E W j ω‖]
      calc c * (s * vecNorm ((M ω)ᴴ *ᵥ nearL b E W j β ω h)) ≤ c * (s * F (ω, h)) := by gcongr
        _ = c * s * F (ω, h) := by ring

end BirthP

/-- **`ComplexBirthKFreshCross` from the input hypotheses** (`GaussianAbsorptionContract`,
`ScalarRecursionContract`, `GaussianLpGradient`).
-/
theorem complexBirthKFreshCross_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) : ComplexBirthKFreshCross := by
  intro b E np τ m T s hD hs _ θ hθ a a' haa
  obtain ⟨hb0, hb, hE1, hE2, hinj, hτ, hm, -⟩ := hD
  obtain ⟨hκ, hE⟩ := BirthP.mem_bulkInterval_min hE1 hE2
  set κ := min (E + 2) (2 - E)
  have hFS := BlockBand.Transmission.EnergyUniform.fullSourceMomentsEnergyUniform_holds hGA hLp
    hSR
  obtain ⟨CΔ, W₁, hCΔ, hΔ⟩ := momBd_stepDelta hGA hb0 hb hκ (r := 2) one_le_two
  obtain ⟨A, W₂, hA, hfr⟩ := momBd_frame hFS hb0 hb hκ T (r := 2) le_rfl
  set e := ((1 - b) * κ / 4)⁻¹
  have he : 0 ≤ e := by
    have : 0 < 1 - b := by linarith
    positivity
  set C := (|1| + e * CΔ) * A
  have hC : 0 ≤ C := by positivity
  set c := Real.sqrt (m a) * Real.sqrt (m a')
  have hsq : Tendsto (fun W : ℕ => Real.sqrt (1 / W)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Real.sqrt_zero] at h
    exact h
  have hlim : Tendsto (fun W : ℕ => c * Real.sqrt (1 / W) * C) atTop (𝓝 0) := by
    simpa using (hsq.const_mul c).mul_const C
  filter_upwards [eventually_ge_atTop (max (max W₁ W₂) 1), (tendsto_order.1 hlim).2 θ hθ,
    BirthP.eventually_one_le_closeLen hs,
    BirthP.eventually_floor_ne (hτ a) (hτ a') (hinj.ne haa)] with W hW hsmall hcl hne
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hW₂⟩, hW1⟩ := hW
  intro j hj1 hj2 hnew
  have hj : 1 ≤ j := hcl.trans hj1
  have hjT := BirthP.le_mul_of_lt_floor hj2
  have hR := BirthP.ae_norm_stepR_le (W := W) hb0 hb hκ hE j
  -- moment bounds for the old tag `k` born at `β < j`
  have hmom : ∀ (k : Fin np), ⌊(W : ℝ) * τ k⌋₊ < j →
      MomBd ((growthPathLaw W b).prod (circularVectorLaw (Fin W))) (fun w =>
        (1 + e * ‖stepDelta b E W j w.1‖) *
          vecNorm (nearL b E W j ⌊(W : ℝ) * τ k⌋₊ w.1 w.2)) 1 C ∧
      MomBd ((growthPathLaw W b).prod (circularVectorLaw (Fin W))) (fun w =>
        (1 + e * ‖stepDelta b E W j w.1‖) *
          vecNorm (nearR b E W j ⌊(W : ℝ) * τ k⌋₊ w.1 w.2)) 1 C := by
    intro k hk
    have hD1 : MomBd ((growthPathLaw W b).prod (circularVectorLaw (Fin W)))
        (fun w => 1 + e * ‖stepDelta b E W j w.1‖) (2 * 1) (|1| + e * CΔ) := by
      rw [mul_one]
      exact (MomBd.const (1 : ℝ) 2 two_pos).add one_le_two
        ((MomBd.comp_fst (hΔ W hW₁ E hE j)).const_mul he) (abs_nonneg _) (by positivity)
    have hfk := hfr W hW₂ E hE j ⌊(W : ℝ) * τ k⌋₊ hk hjT (Fin W → ℂ) (circularVectorLaw (Fin W))
      id measurable_id (Measure.map_id)
    have hL := momBd_nearL_of_frame measurable_id hfk
    have hRr := momBd_nearR_of_frame measurable_id hfk
    refine ⟨hD1.mul one_pos ?_ (by positivity), hD1.mul one_pos ?_ (by positivity)⟩
    · rw [mul_one]; exact hL
    · rw [mul_one]; exact hRr
  have hzero : ∀ (k k' : Fin np), j < ⌊(W : ℝ) * τ k'⌋₊ →
      ∫⁻ x, ‖complexSourceK b E W (j + 1) τ m x k k'‖ₑ ∂probedPathLaw W np b = 0 ∧
      ∫⁻ x, ‖complexSourceK b E W (j + 1) τ m x k' k‖ₑ ∂probedPathLaw W np b = 0 := by
    intro k k' hk'
    constructor
    · simp [Birth.complexSourceK_unborn_col (b := b) (E := E) (m := m) (show j + 1 ≤
        ⌊(W : ℝ) * τ k'⌋₊ by omega)]
    · simp [Birth.complexSourceK_unborn_row (b := b) (E := E) (m := m) (show j + 1 ≤
        ⌊(W : ℝ) * τ k'⌋₊ by omega)]
  have hsmall' : ENNReal.ofReal (c * Real.sqrt (1 / W) * C) ≤ ENNReal.ofReal θ :=
    ENNReal.ofReal_le_ofReal hsmall.le
  rcases hnew with ha | ha'
  · -- `a` is newborn
    rcases lt_trichotomy ⌊(W : ℝ) * τ a'⌋₊ j with hk | hk | hk
    · obtain ⟨hL, hRr⟩ := hmom a' hk
      exact ((BirthP.lintegral_kc_cross_le hb0 hb hE1 hE2 hW1 τ m hm haa hj ha hk he hC hR hL
        hRr).1).trans hsmall'
    · exact absurd (ha.trans hk.symm) hne
    · rw [(hzero a a' hk).1]; positivity
  · -- `a'` is newborn
    rcases lt_trichotomy ⌊(W : ℝ) * τ a⌋₊ j with hk | hk | hk
    · obtain ⟨hL, hRr⟩ := hmom a hk
      have := (BirthP.lintegral_kc_cross_le hb0 hb hE1 hE2 hW1 τ m hm (Ne.symm haa) hj ha' hk he
        hC hR hL hRr).2
      refine this.trans (le_of_eq_of_le ?_ hsmall')
      rw [show Real.sqrt (m a') * Real.sqrt (m a) = c by rw [mul_comm]]
    · exact absurd (hk.trans ha'.symm) hne
    · rw [(hzero a' a hk).2]; positivity

end BlockBand.SourceProcess.PhysApprox.B3
