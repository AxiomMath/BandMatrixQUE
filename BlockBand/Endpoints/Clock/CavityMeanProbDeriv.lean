module

public import BlockBand.Endpoints.Clock.CavityMeanProbFluct
public import BlockBand.Endpoints.Clock.CavityMeanProbAnalytic
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The cavity-mean lemma (iv): the same bounds for every fixed `z'`-derivative

We prove the mean and fluctuation bounds of the cavity-mean lemma for every fixed derivative
`∂^k_{z'}` (`cavityMean_deriv`).

Proof. Fix `k`, the domain `Im z' ≥ η₀`, `|z'| ≤ M`, and the circle of radius
`r = η₀/2` around `z'`; it lies in the larger domain `Im ≥ η₀/2`, `|·| ≤ M + η₀/2`, to which (ii)
and (iii) are applied. Almost surely `ζ ↦ h₊(ζ)` is holomorphic on the upper half-plane
(`normalizedResolventTrace_differentiableOn`, `X₊` Hermitian), and so is `u`
(`cavityU_differentiableOn`). Cauchy's formula
(`DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul`) writes each `k`-th derivative as
`k!/(2πi) ∮ (ζ - z')^{-(k+1)} (·)(ζ) dζ`.
* Mean: Fubini (`integral_circleIntegral_comm`, `h₊` is bounded by `2/η₀` on the circle) gives
  `E ∂^k h₊(z') = k!/(2πi) ∮ (ζ - z')^{-(k+1)} E h₊(ζ) dζ`, so
  `|E ∂^k h₊(z') - ∂^k u(z')| ≤ k! r^{-k} sup_circle |E h₊ - u| ≤ k! r^{-k} C₂ W⁻²`.
* Fluctuation: `∂^k h₊ - E ∂^k h₊ = k!/(2πi) ∮ (ζ - z')^{-(k+1)} (h₊(ζ) - E h₊(ζ)) dζ` a.s., and the
  integral form of Minkowski's inequality (`eLpNorm_integral_le_measure_mul`, proved here for a
  finite parameter measure from Hölder and Tonelli) moves the bound (iii) inside:
  `‖∂^k h₊ - E ∂^k h₊‖_p ≤ k! r^{-k} C₃ √p/W` for `2 ≤ p ≤ a₀ W`.

Interior points. The bounds are proved uniformly on the whole closed domain `Im z' ≥ η₀`,
`|z'| ≤ M`; every point of it is interior to the larger domain `Im ≥ η₀/2`, `|·| ≤ M + η₀/2`, so the bounds hold at
interior points, with constants depending on `k` and the domain only (`a₀` is that of (iii) on the
larger domain). The mean is stated as `E(∂^k h₊(z') | X)` (the
conditional mean of the derivative), which is the form used by the fluctuation clause.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology Metric
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements (freshSchur)
open scoped ENNReal Real

namespace CavityMeanProb

/-!
## Integral Minkowski inequality for a finite parameter measure
-/

/-- **Minkowski's integral inequality** (finite parameter measure, `q ≥ 1`):
`‖∫ G(θ, ·) dν(θ)‖_{L^q(μ)} ≤ ν(Θ) sup_θ ‖G(θ, ·)‖_{L^q(μ)}`. -/
theorem eLpNorm_integral_le_measure_mul {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    {μ : Measure Ω} [SFinite μ] {ν : Measure Θ} [IsFiniteMeasure ν] {G : Θ → Ω → ℂ}
    (hG : Measurable (fun q : Ω × Θ => G q.2 q.1)) {q : ℝ} (hq : 1 ≤ q) {B : ℝ≥0∞}
    (hB : ∀ θ, eLpNorm (G θ) (ENNReal.ofReal q) μ ≤ B) :
    eLpNorm (fun ω => ∫ θ, G θ ω ∂ν) (ENNReal.ofReal q) μ ≤ ν Set.univ * B := by
  rcases eq_or_ne (ν Set.univ) 0 with h0 | h0
  · have hν : ν = 0 := Measure.measure_univ_eq_zero.mp h0
    subst hν
    simp
  set P := ENNReal.ofReal q with hPdef
  have hq0 : 0 < q := by linarith
  have hP0 : P ≠ 0 := by
    rw [hPdef]; exact (ENNReal.ofReal_pos.mpr hq0).ne'
  have hPtop : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hPr : P.toReal = q := ENNReal.toReal_ofReal hq0.le
  have hsec1 : ∀ θ, Measurable (G θ) := fun θ =>
    hG.comp (measurable_id.prodMk measurable_const)
  have hsec2 : ∀ ω, Measurable (fun θ => G θ ω) := fun ω =>
    hG.comp (measurable_const.prodMk measurable_id)
  have hmeasI : AEStronglyMeasurable (fun ω => ∫ θ, G θ ω ∂ν) μ :=
    hG.aestronglyMeasurable.integral_prod_right'
  have hνtop : ν Set.univ ≠ ⊤ := measure_ne_top ν Set.univ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop hmeasI, hPr]
  -- pointwise Hölder in `θ`
  have hpt : ∀ ω, ‖∫ θ, G θ ω ∂ν‖ₑ ^ q ≤ (∫⁻ θ, ‖G θ ω‖ₑ ^ q ∂ν) * ν Set.univ ^ (q - 1) := by
    intro ω
    have h1 := enorm_integral_le_lintegral_enorm (μ := ν) (fun θ => G θ ω)
    have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos (μ := ν) (f := fun θ => G θ ω)
      (p := 1) (q := P) (by rw [hPdef]; exact ENNReal.one_le_ofReal.mpr hq) one_pos
    have hm2 : AEStronglyMeasurable (fun θ => G θ ω) ν := (hsec2 ω).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hm2, eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop hm2, hPr,
      ENNReal.toReal_one] at h2
    calc ‖∫ θ, G θ ω ∂ν‖ₑ ^ q
        ≤ ((∫⁻ θ, ‖G θ ω‖ₑ ^ q ∂ν) ^ (1 / q) * ν Set.univ ^ (1 / 1 - 1 / q)) ^ q :=
          ENNReal.rpow_le_rpow (h1.trans h2) hq0.le
      _ = (∫⁻ θ, ‖G θ ω‖ₑ ^ q ∂ν) * ν Set.univ ^ (q - 1) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          have e1 : 1 / q * q = 1 := by field_simp
          have e2 : (1 / 1 - 1 / q) * q = q - 1 := by field_simp
          rw [e1, e2, ENNReal.rpow_one]
  have hθ : ∀ θ, ∫⁻ ω, ‖G θ ω‖ₑ ^ q ∂μ ≤ B ^ q := by
    intro θ
    have h := hB θ
    have hm1 : AEStronglyMeasurable (G θ) μ := (hsec1 θ).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop hm1, hPr] at h
    have h' := ENNReal.rpow_le_rpow h hq0.le
    rwa [← ENNReal.rpow_mul, show 1 / q * q = 1 by field_simp, ENNReal.rpow_one] at h'
  have hswap : ∫⁻ ω, ∫⁻ θ, ‖G θ ω‖ₑ ^ q ∂ν ∂μ = ∫⁻ θ, ∫⁻ ω, ‖G θ ω‖ₑ ^ q ∂μ ∂ν :=
    lintegral_lintegral_swap (f := fun ω θ => ‖G θ ω‖ₑ ^ q)
      ((hG.enorm.pow_const q).aemeasurable)
  have hint : ∫⁻ ω, ‖∫ θ, G θ ω ∂ν‖ₑ ^ q ∂μ ≤ (ν Set.univ * B) ^ q := by
    calc ∫⁻ ω, ‖∫ θ, G θ ω ∂ν‖ₑ ^ q ∂μ
        ≤ ∫⁻ ω, (∫⁻ θ, ‖G θ ω‖ₑ ^ q ∂ν) * ν Set.univ ^ (q - 1) ∂μ := lintegral_mono hpt
      _ = (∫⁻ ω, ∫⁻ θ, ‖G θ ω‖ₑ ^ q ∂ν ∂μ) * ν Set.univ ^ (q - 1) :=
          lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hνtop)
      _ = (∫⁻ θ, ∫⁻ ω, ‖G θ ω‖ₑ ^ q ∂μ ∂ν) * ν Set.univ ^ (q - 1) := by rw [hswap]
      _ ≤ (∫⁻ _θ, B ^ q ∂ν) * ν Set.univ ^ (q - 1) := by
          gcongr with θ
          exact hθ θ
      _ = (ν Set.univ * B) ^ q := by
          rw [lintegral_const, ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
          have : ν Set.univ * ν Set.univ ^ (q - 1) = ν Set.univ ^ q := by
            rw [show ν Set.univ * ν Set.univ ^ (q - 1) =
                ν Set.univ ^ (1 : ℝ) * ν Set.univ ^ (q - 1) by rw [ENNReal.rpow_one],
              ← ENNReal.rpow_add _ _ h0 hνtop]
            congr 1; ring
          rw [← this]; ring
  calc (∫⁻ ω, ‖∫ θ, G θ ω ∂ν‖ₑ ^ q ∂μ) ^ (1 / q) ≤ ((ν Set.univ * B) ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = ν Set.univ * B := by
        rw [← ENNReal.rpow_mul, show q * (1 / q) = 1 by field_simp, ENNReal.rpow_one]

/-!
## Fubini for circle integrals
-/

theorem continuous_deriv_circleMap (c : ℂ) (R : ℝ) :
    Continuous (fun θ : ℝ => deriv (circleMap c R) θ) := by
  have h : (fun θ : ℝ => deriv (circleMap c R) θ) = fun θ => circleMap 0 R θ * Complex.I :=
    funext (deriv_circleMap c R)
  rw [h]
  exact (continuous_circleMap 0 R).mul continuous_const

theorem norm_deriv_circleMap {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    ‖deriv (circleMap c R) θ‖ = R := by
  rw [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_nonneg hR]

instance isFiniteMeasure_restrict_Ioc_twoPi :
    IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
  isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne

/-- **Fubini for a circle integral** of a jointly measurable function bounded on the circle
for a.e. `ω`: `E ∮ F(ζ, ·) dζ = ∮ E F(ζ, ·) dζ`. -/
theorem integral_circleIntegral_comm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {F : ℂ → Ω → ℂ} (hF : Measurable (fun q : ℂ × Ω => F q.1 q.2)) (c : ℂ)
    {R : ℝ} (hR : 0 ≤ R) {B : ℝ} (hB : ∀ᵐ ω ∂μ, ∀ ζ ∈ sphere c R, ‖F ζ ω‖ ≤ B) :
    ∫ ω, (∮ ζ in C(c, R), F ζ ω) ∂μ = ∮ ζ in C(c, R), ∫ ω, F ζ ω ∂μ := by
  have h2π : (0 : ℝ) ≤ 2 * π := Real.two_pi_pos.le
  simp only [circleIntegral, intervalIntegral.integral_of_le h2π]
  set ν := volume.restrict (Set.Ioc (0 : ℝ) (2 * π))
  have hmeas : Measurable (fun q : Ω × ℝ => deriv (circleMap c R) q.2 • F (circleMap c R q.2) q.1) :=
    ((continuous_deriv_circleMap c R).measurable.comp measurable_snd).smul
      (hF.comp (((continuous_circleMap c R).measurable.comp measurable_snd).prodMk measurable_fst))
  have hint : Integrable (Function.uncurry fun ω θ => deriv (circleMap c R) θ •
      F (circleMap c R θ) ω) (μ.prod ν) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (R * B) ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hB] with q hq
    show ‖deriv (circleMap c R) q.2 • F (circleMap c R q.2) q.1‖ ≤ R * B
    rw [norm_smul, norm_deriv_circleMap hR]
    exact mul_le_mul_of_nonneg_left (hq _ (circleMap_mem_sphere c hR q.2)) hR
  rw [integral_integral_swap hint]
  congr 1
  funext θ
  exact integral_smul _ _

/-!
## Holomorphy and continuity of `h₊` and of its mean
-/

theorem normalizedResolventTrace_differentiableOn {W : ℕ}
    {Y : Matrix (Fin W) (Fin W) ℂ} (hY : Y.IsHermitian) :
    DifferentiableOn ℂ (normalizedResolventTrace Y) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have heq : cavityStieltjes (fun _ => (W : ℝ)⁻¹) hY.eigenvalues =ᶠ[𝓝 z]
      normalizedResolventTrace Y := by
    filter_upwards [hopen.mem_nhds hz] with ζ hζ
    exact (normalizedResolventTrace_eq hY (ne_of_gt hζ)).symm
  have hd : DifferentiableAt ℂ (cavityStieltjes (fun _ => (W : ℝ)⁻¹) hY.eigenvalues) z := by
    unfold cavityStieltjes
    refine DifferentiableAt.fun_sum fun i _ => ?_
    exact (differentiableAt_const _).mul
      ((differentiableAt_id.sub_const _).inv (CavityMean.sub_ofReal_ne_zero hz _))
  exact (hd.congr_of_eventuallyEq heq.symm).differentiableWithinAt

theorem continuousOn_integral_cavityHplus {W : ℕ} (hW : 0 < W) (b e : ℝ)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) {η : ℝ} (hη : 0 < η) :
    ContinuousOn (fun ζ => ∫ ω, cavityHplus e X ζ ω ∂layerLaw W b .oneBlockOnePort)
      {ζ : ℂ | η ≤ ζ.im} := by
  refine continuousOn_of_dominated (bound := fun _ => 1 / η)
    (fun ζ _ => (measurable_cavityHplus e X ζ).aestronglyMeasurable) ?_ (integrable_const _) ?_
  · intro ζ hζ
    filter_upwards [ae_freshSchur_isHermitian W b e hX] with ω hω
    exact (norm_cavityHplus_le hW e hω (hη.trans_le hζ)).trans
      (one_div_le_one_div_of_le hη hζ)
  · filter_upwards [ae_freshSchur_isHermitian W b e hX] with ω hω
    exact ((normalizedResolventTrace_differentiableOn hω).continuousOn).mono
      fun ζ hζ => hη.trans_le hζ

/-- The Cauchy constant `(2πi / k!)⁻¹ = k! / (2πi)`. -/
def cauchyConst (k : ℕ) : ℂ := (2 * π * Complex.I / k.factorial)⁻¹

theorem cauchyConst_eq (k : ℕ) : cauchyConst k = (k.factorial : ℂ) * (2 * π * Complex.I)⁻¹ := by
  unfold cauchyConst
  rw [_root_.inv_div, div_eq_mul_inv]

theorem norm_cauchyConst (k : ℕ) : ‖cauchyConst k‖ = k.factorial / (2 * π) := by
  have h1 : ‖(2 * (π : ℂ) * Complex.I)‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  rw [cauchyConst_eq, norm_mul, norm_inv, h1, Complex.norm_natCast]
  ring

/-- **Cauchy's formula for the `k`-th derivative** on a closed disc in the upper half-plane. -/
theorem iteratedDeriv_eq_cauchy {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (k : ℕ) {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hball : closedBall z₀ r ⊆ {z : ℂ | 0 < z.im}) :
    iteratedDeriv k f z₀ = cauchyConst k • ∮ ζ in C(z₀, r), (1 / (ζ - z₀) ^ (k + 1)) • f ζ := by
  rw [(hf.mono hball).circleIntegral_one_div_sub_center_pow_smul hr k, cauchyConst, smul_smul,
    inv_mul_cancel₀ (by simp [Nat.factorial_ne_zero, Real.pi_ne_zero]), one_smul]

theorem measurable_cauchyWeight (z₀ : ℂ) (k : ℕ) :
    Measurable (fun ζ : ℂ => 1 / (ζ - z₀) ^ (k + 1)) := by
  have h : (fun ζ : ℂ => 1 / (ζ - z₀) ^ (k + 1)) = fun ζ => ((ζ - z₀) ^ (k + 1))⁻¹ := by
    funext ζ; rw [one_div]
  rw [h]
  exact ((measurable_id'.sub_const z₀).pow_const (k + 1)).inv

theorem norm_cauchyWeight {z₀ ζ : ℂ} {r : ℝ} (hζ : ζ ∈ sphere z₀ r) (k : ℕ) :
    ‖1 / (ζ - z₀) ^ (k + 1)‖ = (1 / r) ^ (k + 1) := by
  rw [mem_sphere_iff_norm] at hζ
  rw [norm_div, norm_one, norm_pow, hζ, ← _root_.one_div_pow]

/-- The disc `closedBall z' (η₀/2)` lies in `Im > 0`; its boundary in the domain
`Im ≥ η₀/2`, `|·| ≤ M + η₀/2`. -/
theorem cauchy_disc {η₀ M : ℝ} {z₀ : ℂ} (hz : η₀ ≤ z₀.im) (hzM : ‖z₀‖ ≤ M) :
    closedBall z₀ (η₀ / 2) ⊆ {z : ℂ | η₀ / 2 ≤ z.im} ∧
      ∀ ζ ∈ sphere z₀ (η₀ / 2), η₀ / 2 ≤ ζ.im ∧ ‖ζ‖ ≤ M + η₀ / 2 := by
  have key : ∀ ζ, ‖ζ - z₀‖ ≤ η₀ / 2 → η₀ / 2 ≤ ζ.im ∧ ‖ζ‖ ≤ M + η₀ / 2 := by
    intro ζ hζ
    have h1 : |ζ.im - z₀.im| ≤ ‖ζ - z₀‖ := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    rw [abs_le] at h1
    refine ⟨by linarith, ?_⟩
    calc ‖ζ‖ = ‖z₀ + (ζ - z₀)‖ := by ring_nf
      _ ≤ ‖z₀‖ + ‖ζ - z₀‖ := norm_add_le _ _
      _ ≤ M + η₀ / 2 := by linarith
  refine ⟨fun ζ hζ => (key ζ (by rwa [mem_closedBall, dist_eq_norm] at hζ)).1, fun ζ hζ => ?_⟩
  exact key ζ (by rw [mem_sphere_iff_norm] at hζ; exact hζ.le)

end CavityMeanProb

open CavityMeanProb

/-- **The cavity-mean lemma (iv)**, the derivative bounds. For `0 < b < 1/2`, `η₀ > 0`, `M` and
every fixed derivative order `k` there are `a₀ > 0` and `C` such that for every `W ≥ 1`, Hermitian
`X`, real `e` (held fixed) and `z'` with `Im z' ≥ η₀`, `|z'| ≤ M`:
* `|E(∂^k_{z'} h₊(z') | X) - ∂^k u(z')| ≤ C W⁻²`, `u = cavityU X b e` the solution of the cavity
  equations;
* `‖∂^k h₊(z') - E(∂^k h₊(z') | X)‖_{L^p} ≤ C √p / W` for `2 ≤ p ≤ a₀ W`.

Expectations and `L^p` norms are over `layerLaw W b .oneBlockOnePort` (conditional on `X`). -/
theorem cavityMean_deriv (habs : GaussianAbsorptionContract) (htm : TraceMatrixContract)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {η₀ M : ℝ} (hη : 0 < η₀) (k : ℕ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ (e : ℝ) (z' : ℂ), η₀ ≤ z'.im → ‖z'‖ ≤ M →
        ‖(∫ ω, iteratedDeriv k (fun ζ => cavityHplus e X ζ ω) z' ∂layerLaw W b .oneBlockOnePort) -
            iteratedDeriv k (cavityU X b e) z'‖ ≤ C / (W : ℝ) ^ 2 ∧
        ∀ p : ℝ, 2 ≤ p → p ≤ a₀ * W →
          eLpNorm (fun ω => iteratedDeriv k (fun ζ => cavityHplus e X ζ ω) z' -
              ∫ ω', iteratedDeriv k (fun ζ => cavityHplus e X ζ ω') z'
                ∂layerLaw W b .oneBlockOnePort)
            (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
            ENNReal.ofReal (C * Real.sqrt p / W) := by
  have hη₁ : 0 < η₀ / 2 := by positivity
  obtain ⟨C₂, hC₂, hmean⟩ := cavityMean_condMean habs hb0 hb1 (M := M + η₀ / 2) hη₁
  obtain ⟨a₀, C₃, ha₀, hfl⟩ := cavityMean_fluctuation htm hb0 hb1 (M := M + η₀ / 2) hη₁
  set r : ℝ := η₀ / 2 with hrdef
  have hr : 0 < r := hη₁
  set C₃' : ℝ := max C₃ 0 with hC₃'
  have hC₃'0 : 0 ≤ C₃' := le_max_right _ _
  set Cd : ℝ := (k.factorial : ℝ) * (1 / r) ^ k * (C₂ + C₃') with hCd
  refine ⟨a₀, Cd, ha₀, fun W hW X hX e z₀ hz hzM => ?_⟩
  set μ := layerLaw W b .oneBlockOnePort with hμ
  set H : ℂ → LayerSample W .oneBlockOnePort → ℂ := fun ζ ω => cavityHplus e X ζ ω with hHdef
  set Hm : ℂ → ℂ := fun ζ => ∫ ω, H ζ ω ∂μ with hHmdef
  set w : ℂ → ℂ := fun ζ => 1 / (ζ - z₀) ^ (k + 1) with hwdef
  set U := cavityU X b e with hUdef
  set Λ := cauchyConst k with hΛ
  obtain ⟨hball', hsph⟩ := cauchy_disc hz hzM
  have hball : closedBall z₀ r ⊆ {z : ℂ | 0 < z.im} := fun ζ hζ => hη₁.trans_le (hball' hζ)
  have hsph_im : ∀ ζ ∈ sphere z₀ r, 0 < ζ.im := fun ζ hζ => hη₁.trans_le (hsph ζ hζ).1
  have hHdiff : ∀ᵐ ω ∂μ, DifferentiableOn ℂ (fun ζ => H ζ ω) {z : ℂ | 0 < z.im} := by
    filter_upwards [ae_freshSchur_isHermitian W b e hX] with ω hω
    exact normalizedResolventTrace_differentiableOn hω
  have hUdiff : DifferentiableOn ℂ U {z : ℂ | 0 < z.im} := cavityU_differentiableOn hW hX hb0 hb1 e
  have hrepH : ∀ᵐ ω ∂μ, iteratedDeriv k (fun ζ => H ζ ω) z₀ =
      Λ • ∮ ζ in C(z₀, r), w ζ • H ζ ω := by
    filter_upwards [hHdiff] with ω hω
    exact iteratedDeriv_eq_cauchy hω k hr hball
  have hrepU : iteratedDeriv k U z₀ = Λ • ∮ ζ in C(z₀, r), w ζ • U ζ :=
    iteratedDeriv_eq_cauchy hUdiff k hr hball
  -- Fubini
  have hHbound : ∀ᵐ ω ∂μ, ∀ ζ ∈ sphere z₀ r, ‖w ζ • H ζ ω‖ ≤ (1 / r) ^ (k + 1) * (1 / r) := by
    filter_upwards [ae_freshSchur_isHermitian W b e hX] with ω hω
    intro ζ hζ
    rw [norm_smul, hwdef, norm_cauchyWeight hζ k]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (norm_cavityHplus_le hW e hω (hsph_im ζ hζ)).trans
      (one_div_le_one_div_of_le hr (hsph ζ hζ).1)
  have hFmeas : Measurable (fun q : ℂ × LayerSample W .oneBlockOnePort => w q.1 • H q.1 q.2) :=
    ((measurable_cauchyWeight z₀ k).comp measurable_fst).smul (measurable_cavityHplus_uncurry e X)
  have hfub : ∫ ω, (∮ ζ in C(z₀, r), w ζ • H ζ ω) ∂μ = ∮ ζ in C(z₀, r), w ζ • Hm ζ := by
    rw [integral_circleIntegral_comm (F := fun ζ ω => w ζ • H ζ ω) hFmeas z₀ hr.le hHbound]
    congr 1
    funext ζ
    exact integral_smul _ _
  have hED : ∫ ω, iteratedDeriv k (fun ζ => H ζ ω) z₀ ∂μ = Λ • ∮ ζ in C(z₀, r), w ζ • Hm ζ := by
    rw [integral_congr_ae hrepH, integral_smul, hfub]
  -- continuity and circle integrability
  have hHmc : ContinuousOn Hm (sphere z₀ r) :=
    (continuousOn_integral_cavityHplus hW b e hX hη₁).mono fun ζ hζ => (hsph ζ hζ).1
  have hwc : ContinuousOn w (sphere z₀ r) := by
    refine ContinuousOn.div continuousOn_const ((continuousOn_id.sub continuousOn_const).pow _) ?_
    intro ζ hζ
    refine pow_ne_zero _ (sub_ne_zero.mpr ?_)
    rintro rfl
    rw [mem_sphere, dist_self] at hζ
    exact hr.ne' hζ.symm
  have hci_Hm : CircleIntegrable (fun ζ => w ζ • Hm ζ) z₀ r :=
    (hwc.smul hHmc).circleIntegrable hr.le
  have hci_U : CircleIntegrable (fun ζ => w ζ • U ζ) z₀ r :=
    (hwc.smul ((hUdiff.mono fun ζ hζ => hsph_im ζ hζ).continuousOn)).circleIntegrable hr.le
  have hci_H : ∀ᵐ ω ∂μ, CircleIntegrable (fun ζ => w ζ • H ζ ω) z₀ r := by
    filter_upwards [hHdiff] with ω hω
    exact (hwc.smul ((hω.mono fun ζ hζ => hsph_im ζ hζ).continuousOn)).circleIntegrable hr.le
  have hΛn : ‖Λ‖ = k.factorial / (2 * π) := norm_cauchyConst k
  constructor
  · -- the mean
    rw [hED, hrepU, ← smul_sub, ← circleIntegral.integral_sub hci_Hm hci_U, hΛ, cauchyConst_eq,
      mul_smul, norm_smul, Complex.norm_natCast]
    have hb : ∀ ζ ∈ sphere z₀ r, ‖w ζ • Hm ζ - w ζ • U ζ‖ ≤
        (1 / r) ^ (k + 1) * (C₂ / (W : ℝ) ^ 2) := by
      intro ζ hζ
      rw [← smul_sub, norm_smul, hwdef, norm_cauchyWeight hζ k]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact hmean W hW X hX e ζ (cavityV X b e ζ) (cavityU X b e ζ) (hsph ζ hζ).1 (hsph ζ hζ).2
        (cavitySol_spec hW hX hb0 hb1 e (hsph_im ζ hζ))
    have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le hb
    calc (k.factorial : ℝ) * ‖(2 * (π : ℂ) * Complex.I)⁻¹ •
          ∮ ζ in C(z₀, r), (w ζ • Hm ζ - w ζ • U ζ)‖
        ≤ k.factorial * (r * ((1 / r) ^ (k + 1) * (C₂ / (W : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = k.factorial * (1 / r) ^ k * C₂ / (W : ℝ) ^ 2 := by
          have hrk : r * (1 / r) ^ (k + 1) = (1 / r) ^ k := by
            rw [pow_succ]; field_simp
          calc (k.factorial : ℝ) * (r * ((1 / r) ^ (k + 1) * (C₂ / (W : ℝ) ^ 2)))
              = k.factorial * ((r * (1 / r) ^ (k + 1)) * (C₂ / (W : ℝ) ^ 2)) := by ring
            _ = k.factorial * (1 / r) ^ k * C₂ / (W : ℝ) ^ 2 := by rw [hrk]; ring
      _ ≤ Cd / (W : ℝ) ^ 2 := by
          have hWr : (0 : ℝ) < W := by exact_mod_cast hW
          rw [hCd, div_le_div_iff_of_pos_right (by positivity)]
          have : 0 ≤ (k.factorial : ℝ) * (1 / r) ^ k := by positivity
          nlinarith
  · -- the fluctuation
    intro p hp hpW
    set ν := volume.restrict (Set.Ioc (0 : ℝ) (2 * π)) with hν
    set G : ℝ → LayerSample W .oneBlockOnePort → ℂ := fun θ ω =>
      deriv (circleMap z₀ r) θ • (w (circleMap z₀ r θ) •
        (H (circleMap z₀ r θ) ω - Hm (circleMap z₀ r θ))) with hGdef
    have hae : (fun ω => iteratedDeriv k (fun ζ => H ζ ω) z₀ -
        ∫ ω', iteratedDeriv k (fun ζ => H ζ ω') z₀ ∂μ) =ᵐ[μ]
        fun ω => Λ • ∫ θ, G θ ω ∂ν := by
      filter_upwards [hrepH, hci_H] with ω h1 h2
      rw [h1, hED, ← smul_sub, ← circleIntegral.integral_sub h2 hci_Hm]
      congr 1
      rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
      congr 1
      funext θ
      simp only [hGdef, smul_sub]
    rw [eLpNorm_congr_ae hae]
    have hsmul : (fun ω => Λ • ∫ θ, G θ ω ∂ν) = Λ • fun ω => ∫ θ, G θ ω ∂ν := rfl
    rw [hsmul]
    refine eLpNorm_const_smul_le.trans ?_
    -- Minkowski
    have hcm : ∀ θ, circleMap z₀ r θ ∈ sphere z₀ r := circleMap_mem_sphere z₀ hr.le
    have hHmθ : Continuous (fun θ => Hm (circleMap z₀ r θ)) :=
      hHmc.comp_continuous (continuous_circleMap z₀ r) hcm
    have hGmeas : Measurable (fun q : LayerSample W .oneBlockOnePort × ℝ => G q.2 q.1) := by
      have hc2 : Measurable (fun q : LayerSample W .oneBlockOnePort × ℝ => circleMap z₀ r q.2) :=
        (continuous_circleMap z₀ r).measurable.comp measurable_snd
      have hcmq : Measurable (fun q : LayerSample W .oneBlockOnePort × ℝ =>
          (circleMap z₀ r q.2, q.1)) := hc2.prodMk measurable_fst
      have h1 : Measurable (fun q : LayerSample W .oneBlockOnePort × ℝ =>
          cavityHplus e X (circleMap z₀ r q.2) q.1) :=
        (measurable_cavityHplus_uncurry e X).comp
          (f := fun q : LayerSample W .oneBlockOnePort × ℝ => (circleMap z₀ r q.2, q.1)) hcmq
      have h2 : Measurable (fun q : LayerSample W .oneBlockOnePort × ℝ =>
          Hm (circleMap z₀ r q.2)) := hHmθ.measurable.comp measurable_snd
      have h3 : Measurable (fun q : LayerSample W .oneBlockOnePort × ℝ =>
          w (circleMap z₀ r q.2)) := (measurable_cauchyWeight z₀ k).comp hc2
      have h4 : Measurable (fun q : LayerSample W .oneBlockOnePort × ℝ =>
          deriv (circleMap z₀ r) q.2) :=
        (continuous_deriv_circleMap z₀ r).measurable.comp measurable_snd
      exact h4.smul (h3.smul (h1.sub h2))
    have hp1 : (1 : ℝ) ≤ p := by linarith
    have hWr : (0 : ℝ) < W := by exact_mod_cast hW
    set B : ℝ≥0∞ := ENNReal.ofReal (r * (1 / r) ^ (k + 1) * (C₃' * Real.sqrt p / W)) with hBdef
    have hB : ∀ θ, eLpNorm (G θ) (ENNReal.ofReal p) μ ≤ B := by
      intro θ
      have hG : G θ = (deriv (circleMap z₀ r) θ * w (circleMap z₀ r θ)) •
          fun ω => H (circleMap z₀ r θ) ω - Hm (circleMap z₀ r θ) := by
        funext ω; simp only [hGdef, Pi.smul_apply, smul_eq_mul]; ring
      rw [hG]
      refine eLpNorm_const_smul_le.trans ?_
      have hfθ := hfl W hW X hX e (circleMap z₀ r θ) (hsph _ (hcm θ)).1 (hsph _ (hcm θ)).2 p hp hpW
      have hfθ' : eLpNorm (fun ω => H (circleMap z₀ r θ) ω - Hm (circleMap z₀ r θ))
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C₃' * Real.sqrt p / W) :=
        hfθ.trans (ENNReal.ofReal_le_ofReal (by
          have : 0 ≤ Real.sqrt p / W := by positivity
          rw [mul_div_assoc, mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) this))
      have hn : ‖deriv (circleMap z₀ r) θ * w (circleMap z₀ r θ)‖ₑ =
          ENNReal.ofReal (r * (1 / r) ^ (k + 1)) := by
        rw [← ofReal_norm, norm_mul, norm_deriv_circleMap hr.le, hwdef,
          norm_cauchyWeight (hcm θ) k]
      rw [hn, hBdef, ENNReal.ofReal_mul (p := r * (1 / r) ^ (k + 1))
        (q := C₃' * Real.sqrt p / W) (by positivity)]
      gcongr
    have hmink := eLpNorm_integral_le_measure_mul (ν := ν) hGmeas hp1 hB
    have hνu : ν Set.univ = ENNReal.ofReal (2 * π) := by
      rw [hν, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    rw [hνu] at hmink
    calc ‖Λ‖ₑ * eLpNorm (fun ω => ∫ θ, G θ ω ∂ν) (ENNReal.ofReal p) μ
        ≤ ‖Λ‖ₑ * (ENNReal.ofReal (2 * π) * B) := by gcongr
      _ = ENNReal.ofReal (k.factorial / (2 * π) * (2 * π *
            (r * (1 / r) ^ (k + 1) * (C₃' * Real.sqrt p / W)))) := by
          rw [← ofReal_norm, hΛn, hBdef, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Cd * Real.sqrt p / W) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have e1 : (k.factorial : ℝ) / (2 * π) * (2 * π *
              (r * (1 / r) ^ (k + 1) * (C₃' * Real.sqrt p / W))) =
              (k.factorial : ℝ) * (1 / r) ^ k * C₃' * (Real.sqrt p / W) := by
            have hrk : r * (1 / r) ^ (k + 1) = (1 / r) ^ k := by rw [pow_succ]; field_simp
            have hπ : (2 * π) ≠ 0 := by positivity
            calc (k.factorial : ℝ) / (2 * π) * (2 * π *
                  (r * (1 / r) ^ (k + 1) * (C₃' * Real.sqrt p / W)))
                = (k.factorial : ℝ) * (r * (1 / r) ^ (k + 1)) * C₃' * (Real.sqrt p / W) := by
                  field_simp
              _ = _ := by rw [hrk]
          rw [e1, hCd]
          have h1 : 0 ≤ (k.factorial : ℝ) * (1 / r) ^ k := by positivity
          have h2 : 0 ≤ Real.sqrt p / W := by positivity
          have : (k.factorial : ℝ) * (1 / r) ^ k * (C₂ + C₃') * Real.sqrt p / W =
              (k.factorial : ℝ) * (1 / r) ^ k * (C₂ + C₃') * (Real.sqrt p / W) := by ring
          rw [this]
          have : (k.factorial : ℝ) * (1 / r) ^ k * C₃' ≤
              (k.factorial : ℝ) * (1 / r) ^ k * (C₂ + C₃') :=
            mul_le_mul_of_nonneg_left (by linarith) h1
          exact mul_le_mul_of_nonneg_right this h2

end BlockBand.Endpoints.Clock
