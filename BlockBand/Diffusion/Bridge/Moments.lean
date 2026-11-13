module

public import BlockBand.Diffusion.Bridge.Kernel
public import BlockBand.Diffusion.Bridge.Estimates
public import BlockBand.Diffusion.Kernel.McKeanIncrements
public import BlockBand.Diffusion.Kernel.McKeanMoments
public import BlockBand.Diffusion.Kernel.SphereMoreMoments
public import BlockBand.Diffusion.Kernel.SphereMoreSup

/-!
# The bridge moment bound for the base kernel

`D₀ > 0`; Lebesgue measure on `ℝ`, `ℝ × ℝ`; `S = exBaseStrip`; the adapter
`q′ = brKernel D0`; `e = (0, 0)`.

* `brF a b = (b₁ - a₁)⁴ + (b₂ - a₂)⁴` (in `ℝ≥0∞`), with `edist a b ^ 4 ≤ brF a b` for the sup
  metric of `ℝ × ℝ` (`edist_rpow_four_le_brF`), symmetric, `brF a c ≤ 8 (brF a b + brF b c)`;
  `brG a = (1 + a₁)⁴ + 1`.
* Kernel estimates for `q′` (all from the kernel bounds for the two factors):
  `brKernel_incr` (`∫ q′_h(a, b) brF(a, b) db ≤ K h² brG(a)` for `0 < h ≤ t`, every `a`,
  `K = 480√2 D₀² e^{81 D₀ t/4} + 8 D₀²`, from `mk_lintegral_kernelX_incr_le`,
  `sk_kernelY_moment4_le`, the masses `∫ pX = ∫ pY = 1`); `brKernel_mom` (`∫ q′_h(x, ·) brG ≤
  512√2 (1 + x₁)⁴ e^{81 D₀ t/4} + 1` for `x ∈ S`, `0 < h ≤ t`, from
  `mk_lintegral_kernelX_moment_le`); `brKernel_diag` (`q′_h ≤ C` for `t/4 ≤ h ≤ t`, from
  `mk_kernelX_le_diag` on the compact `[D₀t/8, D₀t/2]` and `sk_kernelY_le_inv`);
  `brKernel_corner_pos` (`0 < q′_t(z, (0,0))` for `z ∈ S`, `t > 0`).
* `brBridgeEstimates`: the kernel estimates `BrBridgeEstimates` for `q′`.
* `brKernel_bridgeMomentBound`: for every `z ∈ S` (in particular every boundary start
  `z ≠ (0,0)`) and `t > 0`, `∃ M ≥ 0, BridgeMomentBound volume (brKernel D0) z (0,0) t 4 2 M`
  (`p = 4`, `γ = 2`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set
open scoped ENNReal NNReal

/-!
### The distance and the weight
-/

/-- The fourth-power distance `(b₁ - a₁)⁴ + (b₂ - a₂)⁴`. -/
def brF (a b : ℝ × ℝ) : ℝ≥0∞ := ENNReal.ofReal ((b.1 - a.1) ^ 4 + (b.2 - a.2) ^ 4)

/-- The weight `(1 + a₁)⁴ + 1`. -/
def brG (a : ℝ × ℝ) : ℝ≥0∞ := ENNReal.ofReal ((1 + a.1) ^ 4 + 1)

theorem measurable_brF : Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => brF p.1 p.2 :=
  (by fun_prop : Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
    (p.2.1 - p.1.1) ^ 4 + (p.2.2 - p.1.2) ^ 4).measurable.ennreal_ofReal

theorem measurable_brG : Measurable brG :=
  (by fun_prop : Continuous fun a : ℝ × ℝ => (1 + a.1) ^ 4 + 1).measurable.ennreal_ofReal

theorem brF_symm (a b : ℝ × ℝ) : brF a b = brF b a := by
  unfold brF
  congr 1
  ring

theorem br_pow_four_add_le (u v : ℝ) : (u + v) ^ 4 ≤ 8 * (u ^ 4 + v ^ 4) := by
  nlinarith [mul_nonneg (sq_nonneg (u - v)) (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5)
    (sq_nonneg (u + v))) (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg u))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg v))))]

theorem brF_tri (a b c : ℝ × ℝ) : brF a c ≤ 8 * (brF a b + brF b c) := by
  unfold brF
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 8,
    ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := br_pow_four_add_le (b.1 - a.1) (c.1 - b.1)
  have h2 := br_pow_four_add_le (b.2 - a.2) (c.2 - b.2)
  rw [show b.1 - a.1 + (c.1 - b.1) = c.1 - a.1 by ring] at h1
  rw [show b.2 - a.2 + (c.2 - b.2) = c.2 - a.2 by ring] at h2
  linarith

theorem br_abs_pow_four (u : ℝ) : |u| ^ 4 = u ^ 4 := Even.pow_abs ⟨2, rfl⟩ u

/-- `edist a b ^ 4 ≤ brF a b` for the sup metric on `ℝ × ℝ`. -/
theorem edist_rpow_four_le_brF (a b : ℝ × ℝ) : edist a b ^ (4 : ℝ) ≤ brF a b := by
  rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num), brF]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Prod.dist_eq,
    Real.dist_eq, Real.dist_eq]
  have h1 : |a.1 - b.1| ^ 4 = (b.1 - a.1) ^ 4 := by rw [br_abs_pow_four]; ring
  have h2 : |a.2 - b.2| ^ 4 = (b.2 - a.2) ^ 4 := by rw [br_abs_pow_four]; ring
  have h3 : 0 ≤ (b.1 - a.1) ^ 4 := by positivity
  have h4 : 0 ≤ (b.2 - a.2) ^ 4 := by positivity
  rcases le_total |a.1 - b.1| |a.2 - b.2| with h | h
  · rw [max_eq_right h, h2]
    linarith
  · rw [max_eq_left h, h1]
    linarith

/-!
### One-dimensional integrals over the whole line
-/

theorem br_mk_support_subset (D0 h x : ℝ) (φ : ℝ → ℝ) :
    (fun x' => ENNReal.ofReal (mkKernelX D0 h x x' * φ x')).support ⊆ Ici 0 := by
  intro x' hx'
  by_contra hn
  have : ¬ 0 ≤ x' := hn
  exact hx' (by simp [mkKernelX, this])

theorem br_lintegral_kernelX_incr {D0 h x : ℝ} (hD0 : 0 < D0) (hh : 0 < h) (hx : 0 ≤ x) :
    ∫⁻ x', ENNReal.ofReal (mkKernelX D0 h x x' * (x' - x) ^ 4) ≤
      ENNReal.ofReal (480 * Real.sqrt 2 * (1 + x) ^ 4 * (D0 * h) ^ 2 *
        Real.exp (81 * (D0 * h) / 4)) := by
  rw [← setLIntegral_eq_of_support_subset (br_mk_support_subset D0 h x fun x' => (x' - x) ^ 4)]
  exact mk_lintegral_kernelX_incr_le hD0 hh hx

theorem br_lintegral_kernelX_moment {D0 h x : ℝ} (hD0 : 0 < D0) (hh : 0 < h) (hx : 0 ≤ x) :
    ∫⁻ x', ENNReal.ofReal (mkKernelX D0 h x x' * (1 + x') ^ 4) ≤
      ENNReal.ofReal (2 * Real.sqrt 2 * 4 ^ 4 * (1 + x) ^ 4 *
        Real.exp ((((4 : ℕ) : ℝ) + 1 / 2) ^ 2 * D0 * h)) := by
  rw [← setLIntegral_eq_of_support_subset (br_mk_support_subset D0 h x fun x' => (1 + x') ^ 4)]
  exact mk_lintegral_kernelX_moment_le hD0 hh hx 4

theorem br_lintegral_kernelX_one {D0 h x : ℝ} (hD0 : 0 < D0) (hh : 0 < h) (hx : 0 ≤ x) :
    ∫⁻ x', ENNReal.ofReal (mkKernelX D0 h x x') = 1 := by
  have := br_mk_support_subset D0 h x fun _ => 1
  simp only [mul_one] at this
  rw [← setLIntegral_eq_of_support_subset this]
  exact mk_lintegral_kernelX hD0 hh hx

theorem br_lintegral_kernelY_moment4 {D0 h y : ℝ} (hD0 : 0 < D0) (hh : 0 < h)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    ∫⁻ y', ENNReal.ofReal ((y' - y) ^ 4 * skKernelY D0 h y y') ≤
      ENNReal.ofReal (8 * D0 ^ 2 * h ^ 2) := by
  have hint : Integrable fun y' => (y' - y) ^ 4 * skKernelY D0 h y y' := by
    refine (sk_integrable_kernelY hD0 h y).mono'
      (((by fun_prop : Continuous fun y' : ℝ => (y' - y) ^ 4).measurable.mul
        (sk_kernelY_measurable_right hD0 h y)).aestronglyMeasurable) (ae_of_all _ fun y' => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sk_kernelY_nonneg hD0 _ _ _)]
    by_cases hy' : y' ∈ Icc (0 : ℝ) 1
    · have h1 : |(y' - y) ^ 4| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]
        have : |y' - y| ≤ 1 := abs_le.2 ⟨by linarith [hy.2, hy'.1], by linarith [hy.1, hy'.2]⟩
        rw [← br_abs_pow_four]
        exact pow_le_one₀ (abs_nonneg _) this
      calc |(y' - y) ^ 4| * skKernelY D0 h y y' ≤ 1 * skKernelY D0 h y y' :=
            mul_le_mul_of_nonneg_right h1 (sk_kernelY_nonneg hD0 _ _ _)
        _ = skKernelY D0 h y y' := one_mul _
    · simp [sk_kernelY_of_notMem_right y hy']
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y' =>
    mul_nonneg (by positivity) (sk_kernelY_nonneg hD0 _ _ _))]
  exact ENNReal.ofReal_le_ofReal (sk_kernelY_moment4_le hD0 hh hy)

theorem br_lintegral_prod_mul {φ ψ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (hψ : Measurable ψ) :
    ∫⁻ b : ℝ × ℝ, φ b.1 * ψ b.2 = (∫⁻ x, φ x) * ∫⁻ y, ψ y := by
  rw [Measure.volume_eq_prod, lintegral_prod_mul hφ.aemeasurable hψ.aemeasurable]

/-!
### The kernel estimates
-/

theorem br_mk_ofReal_meas (D0 h x : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    Measurable fun x' => ENNReal.ofReal (mkKernelX D0 h x x' * φ x') :=
  ((mk_kernelX_measurable_snd D0 h x).mul hφ).ennreal_ofReal

/-- **Increment moment** of the adapter. -/
theorem brKernel_incr {D0 t : ℝ} (hD0 : 0 < D0) {h : ℝ} (hh : 0 < h) (hht : h ≤ t)
    (a : ℝ × ℝ) :
    ∫⁻ b, brKernel D0 h a b * brF a b ≤
      ENNReal.ofReal (480 * Real.sqrt 2 * D0 ^ 2 * Real.exp (81 * (D0 * t) / 4) + 8 * D0 ^ 2) *
        ENNReal.ofReal (h ^ 2) * brG a := by
  by_cases ha : a ∉ exBaseStrip
  · simp [brKernel_of_notMem ha]
  rw [not_not] at ha
  have hX := br_lintegral_kernelX_incr hD0 hh ha.1
  have hY := br_lintegral_kernelY_moment4 hD0 hh ha.2
  have hpt : ∀ b : ℝ × ℝ, brKernel D0 h a b * brF a b =
      ENNReal.ofReal (mkKernelX D0 h a.1 b.1 * (b.1 - a.1) ^ 4) *
          ENNReal.ofReal (skKernelY D0 h a.2 b.2) +
        ENNReal.ofReal (mkKernelX D0 h a.1 b.1) *
          ENNReal.ofReal ((b.2 - a.2) ^ 4 * skKernelY D0 h a.2 b.2) := by
    intro b
    have h1 := mk_kernelX_nonneg hD0 h a.1 b.1
    have h2 := sk_kernelY_nonneg hD0 h a.2 b.2
    rw [brKernel_of_mem ha, exKernel_eq, brF, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hmX1 := br_mk_ofReal_meas D0 h a.1 (fun x' => (x' - a.1) ^ 4) (by fun_prop)
  have hmX0 : Measurable fun x' => ENNReal.ofReal (mkKernelX D0 h a.1 x') :=
    (mk_kernelX_measurable_snd D0 h a.1).ennreal_ofReal
  have hmY0 : Measurable fun y' => ENNReal.ofReal (skKernelY D0 h a.2 y') :=
    (sk_kernelY_measurable_right hD0 h a.2).ennreal_ofReal
  have hmY1 : Measurable fun y' => ENNReal.ofReal ((y' - a.2) ^ 4 * skKernelY D0 h a.2 y') :=
    ((by fun_prop : Measurable fun y' : ℝ => (y' - a.2) ^ 4).mul
      (sk_kernelY_measurable_right hD0 h a.2)).ennreal_ofReal
  have hm1 : Measurable fun b : ℝ × ℝ =>
      ENNReal.ofReal (mkKernelX D0 h a.1 b.1 * (b.1 - a.1) ^ 4) *
        ENNReal.ofReal (skKernelY D0 h a.2 b.2) :=
    (hmX1.comp measurable_fst).mul (hmY0.comp measurable_snd)
  simp_rw [hpt]
  rw [lintegral_add_left hm1, br_lintegral_prod_mul hmX1 hmY0, br_lintegral_prod_mul hmX0 hmY1,
    sk_lintegral_kernelY_one hD0 hh ha.2, br_lintegral_kernelX_one hD0 hh ha.1, mul_one, one_mul]
  refine (add_le_add hX hY).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), brG,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hE : Real.exp (81 * (D0 * h) / 4) ≤ Real.exp (81 * (D0 * t) / 4) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hw : 0 ≤ (1 + a.1) ^ 4 := by positivity
  have hc : 0 ≤ 480 * Real.sqrt 2 * D0 ^ 2 * h ^ 2 := by positivity
  have hd : 0 ≤ D0 ^ 2 * h ^ 2 := by positivity
  have hE0 : 0 ≤ Real.exp (81 * (D0 * t) / 4) := (Real.exp_pos _).le
  have k1 : 480 * Real.sqrt 2 * D0 ^ 2 * h ^ 2 * (1 + a.1) ^ 4 * Real.exp (81 * (D0 * h) / 4) ≤
      480 * Real.sqrt 2 * D0 ^ 2 * h ^ 2 * (1 + a.1) ^ 4 * Real.exp (81 * (D0 * t) / 4) :=
    mul_le_mul_of_nonneg_left hE (mul_nonneg hc hw)
  have k2 : 0 ≤ 480 * Real.sqrt 2 * D0 ^ 2 * h ^ 2 * Real.exp (81 * (D0 * t) / 4) :=
    mul_nonneg hc hE0
  have k3 : 0 ≤ 8 * (D0 ^ 2 * h ^ 2) * (1 + a.1) ^ 4 := by positivity
  have e1 : 480 * Real.sqrt 2 * (1 + a.1) ^ 4 * (D0 * h) ^ 2 * Real.exp (81 * (D0 * h) / 4) =
      480 * Real.sqrt 2 * D0 ^ 2 * h ^ 2 * (1 + a.1) ^ 4 * Real.exp (81 * (D0 * h) / 4) := by
    ring
  have e2 : (480 * Real.sqrt 2 * D0 ^ 2 * Real.exp (81 * (D0 * t) / 4) + 8 * D0 ^ 2) * h ^ 2 *
      ((1 + a.1) ^ 4 + 1) =
      480 * Real.sqrt 2 * D0 ^ 2 * h ^ 2 * (1 + a.1) ^ 4 * Real.exp (81 * (D0 * t) / 4) +
        480 * Real.sqrt 2 * D0 ^ 2 * h ^ 2 * Real.exp (81 * (D0 * t) / 4) +
        8 * (D0 ^ 2 * h ^ 2) * (1 + a.1) ^ 4 + 8 * D0 ^ 2 * h ^ 2 := by ring
  rw [e1, e2]
  linarith

/-- **Weight moment** of the adapter from strip points. -/
theorem brKernel_mom {D0 t : ℝ} (hD0 : 0 < D0) {x : ℝ × ℝ} (hx : x ∈ exBaseStrip) {h : ℝ}
    (hh : 0 < h) (hht : h ≤ t) :
    ∫⁻ a, brKernel D0 h x a * brG a ≤
      ENNReal.ofReal (512 * Real.sqrt 2 * (1 + x.1) ^ 4 * Real.exp (81 * (D0 * t) / 4) + 1) := by
  have hX := br_lintegral_kernelX_moment hD0 hh hx.1
  have hpt : ∀ a : ℝ × ℝ, brKernel D0 h x a * brG a =
      ENNReal.ofReal (mkKernelX D0 h x.1 a.1 * (1 + a.1) ^ 4) *
          ENNReal.ofReal (skKernelY D0 h x.2 a.2) +
        ENNReal.ofReal (mkKernelX D0 h x.1 a.1) * ENNReal.ofReal (skKernelY D0 h x.2 a.2) := by
    intro a
    have h1 := mk_kernelX_nonneg hD0 h x.1 a.1
    have h2 := sk_kernelY_nonneg hD0 h x.2 a.2
    rw [brKernel_of_mem hx, exKernel_eq, brG, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hmX1 := br_mk_ofReal_meas D0 h x.1 (fun x' => (1 + x') ^ 4) (by fun_prop)
  have hmX0 : Measurable fun x' => ENNReal.ofReal (mkKernelX D0 h x.1 x') :=
    (mk_kernelX_measurable_snd D0 h x.1).ennreal_ofReal
  have hmY0 : Measurable fun y' => ENNReal.ofReal (skKernelY D0 h x.2 y') :=
    (sk_kernelY_measurable_right hD0 h x.2).ennreal_ofReal
  have hm1 : Measurable fun b : ℝ × ℝ =>
      ENNReal.ofReal (mkKernelX D0 h x.1 b.1 * (1 + b.1) ^ 4) *
        ENNReal.ofReal (skKernelY D0 h x.2 b.2) :=
    (hmX1.comp measurable_fst).mul (hmY0.comp measurable_snd)
  simp_rw [hpt]
  rw [lintegral_add_left hm1, br_lintegral_prod_mul hmX1 hmY0, br_lintegral_prod_mul hmX0 hmY0,
    sk_lintegral_kernelY_one hD0 hh hx.2, br_lintegral_kernelX_one hD0 hh hx.1, mul_one,
    mul_one]
  refine (add_le_add hX le_rfl).trans ?_
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) zero_le_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have hE : Real.exp ((((4 : ℕ) : ℝ) + 1 / 2) ^ 2 * D0 * h) ≤ Real.exp (81 * (D0 * t) / 4) :=
    Real.exp_le_exp.2 (by push_cast; nlinarith)
  have hw : 0 ≤ (1 + x.1) ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_left hE
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 512 * Real.sqrt 2) hw)
  nlinarith

/-- **On-diagonal bound** for the adapter on `[t/4, t]`. -/
theorem brKernel_diag {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h, t / 4 ≤ h → h ≤ t → ∀ a b, brKernel D0 h a b ≤ ENNReal.ofReal C := by
  have hsub : Icc (D0 * t / 8) (D0 * t / 2) ⊆ Ioi 0 := fun T hT =>
    lt_of_lt_of_le (by positivity) hT.1
  obtain ⟨Cx, hCx⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (mk_diagBound_continuousOn.mono hsub)
  have hDt : 0 < D0 * t := by positivity
  have hCx0 : 0 ≤ Cx := (norm_nonneg _).trans (hCx (D0 * t / 2) ⟨by linarith, le_rfl⟩)
  refine ⟨Cx * (1 + 12 / (D0 * t)), by positivity, fun h h1 h2 a b => ?_⟩
  have hh : 0 < h := lt_of_lt_of_le (by positivity) h1
  refine (brKernel_le_ofReal D0 h a b).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [exKernel_eq]
  have hX : mkKernelX D0 h a.1 b.1 ≤ Cx := by
    refine (mk_kernelX_le_diag hD0 hh _ _).trans ((le_abs_self _).trans ?_)
    rw [← Real.norm_eq_abs]
    exact hCx _ ⟨by nlinarith, by nlinarith⟩
  have hY : skKernelY D0 h a.2 b.2 ≤ 1 + 12 / (D0 * t) := by
    refine (sk_kernelY_le_inv hD0 hh _ _).trans ?_
    have : 3 / (D0 * h) ≤ 12 / (D0 * t) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  exact mul_le_mul hX hY (sk_kernelY_nonneg hD0 _ _ _) hCx0

/-- **Corner positivity**: `0 < q′_t(z, (0,0))` for `z ∈ S`, `t > 0`. -/
theorem brKernel_corner_pos {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) {z : ℝ × ℝ}
    (hz : z ∈ exBaseStrip) : brKernel D0 t z (0, 0) ≠ 0 := by
  rw [brKernel_of_mem hz, exKernel_eq]
  exact (ENNReal.ofReal_pos.2 (mul_pos (mk_kernelX_zero_pos hD0 ht _)
    (sk_kernelY_corner_pos hD0 ht hz.2))).ne'

/-!
### The bridge moment bound
-/

/-- The kernel estimates `BrBridgeEstimates` for the adapter, `f = brF`, `g = brG`, endpoint
`(0, 0)`, any strip start `z`, any `t > 0`. -/
theorem brBridgeEstimates {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) {t : ℝ}
    (ht : 0 < t) :
    ∃ K G C F : ℝ≥0, BrBridgeEstimates volume (brKernel D0) brF brG z (0, 0) t K G C F := by
  obtain ⟨C, hC0, hC⟩ := brKernel_diag hD0 ht
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ exBaseStrip := ⟨le_rfl, le_rfl, zero_le_one⟩
  set E := Real.exp (81 * (D0 * t) / 4) with hE
  refine ⟨(480 * Real.sqrt 2 * D0 ^ 2 * E + 8 * D0 ^ 2).toNNReal,
    (512 * Real.sqrt 2 * ((1 + z.1) ^ 4 + 1) * E + (1 + z.1) ^ 4 + 2).toNNReal, C.toNNReal,
    ((0 - z.1) ^ 4 + (0 - z.2) ^ 4).toNNReal, ?_⟩
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hw : 0 ≤ (1 + z.1) ^ 4 := by positivity
  have hGz : 512 * Real.sqrt 2 * (1 + z.1) ^ 4 * E + 1 ≤
      512 * Real.sqrt 2 * ((1 + z.1) ^ 4 + 1) * E + (1 + z.1) ^ 4 + 2 := by
    have : 0 ≤ 512 * Real.sqrt 2 * E := by positivity
    nlinarith
  have hGe : 512 * Real.sqrt 2 * (1 + (0 : ℝ)) ^ 4 * E + 1 ≤
      512 * Real.sqrt 2 * ((1 + z.1) ^ 4 + 1) * E + (1 + z.1) ^ 4 + 2 := by
    have : 0 ≤ 512 * Real.sqrt 2 * E := by positivity
    nlinarith
  have hS : 0 ≤ 512 * Real.sqrt 2 * ((1 + z.1) ^ 4 + 1) * E := by positivity
  exact
    { meas_q := measurable_brKernel hD0
      ck := brKernel_chapmanKolmogorov hD0
      symm := brKernel_symm D0
      meas_f := measurable_brF
      f_symm := brF_symm
      f_tri := brF_tri
      meas_g := measurable_brG
      incr := fun h hh hht a => brKernel_incr hD0 hh hht a
      mom_z := fun h hh hht => (brKernel_mom hD0 hz hh hht).trans (ENNReal.ofReal_le_ofReal hGz)
      mom_e := fun h hh hht => (brKernel_mom hD0 h0 hh hht).trans (ENNReal.ofReal_le_ofReal hGe)
      one_le_g := fun a => by
        rw [brG, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [pow_two_nonneg ((1 + a.1) ^ 2)])
      g_z := ENNReal.ofReal_le_ofReal (by nlinarith)
      g_e := ENNReal.ofReal_le_ofReal (by norm_num; nlinarith)
      diag := hC
      f_ze := le_rfl }

/-- **The bridge moment bound for the base kernel.** For `D₀ > 0`, every start `z` in the
closed strip, and every `t > 0`, the adapter `q′ = brKernel D0` satisfies the Chentsov
hypothesis `BridgeMomentBound` with endpoint `(0, 0)`, `p = 4`, `γ = 2`. -/
theorem brKernel_bridgeMomentBound {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip)
    {t : ℝ} (ht : 0 < t) :
    ∃ M : ℝ, 0 ≤ M ∧ BridgeMomentBound volume (brKernel D0) z (0, 0) t 4 2 M := by
  obtain ⟨K, G, C, F, H⟩ := brBridgeEstimates hD0 hz ht
  exact H.bridgeMomentBound ht (brKernel_corner_pos hD0 ht hz) edist_rpow_four_le_brF

end BlockBand.Diffusion
