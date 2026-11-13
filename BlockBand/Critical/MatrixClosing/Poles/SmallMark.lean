module

public import BlockBand.Critical.MatrixClosing.Poles.Compare
public import BlockBand.Critical.Herglotz.SineIntensity
public import BlockBand.Coarea.ProjectiveHaar

/-!
# Step, limit side: small marks are rare in the decorated sine process

* `smallMarkTest R t n : C_c(ℝ × ℂ^r)`, `(x, z) ↦ t β_R(x) max(0, 1 - (n+1)‖z‖)`; it equals
  `t β_R(x)` at `z = 0`.
* `tendsto_integral_smallBump` (`r ≥ 1`, `γ_r{0} = 0`) and **`exists_smallMarkTest`**:
  `1 - L(smallMarkTest R t n) ≤ η` for some `n`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.Herglotz

variable {r : ℕ}

/-- The small-mark bump `z ↦ max(0, 1 - (n+1)‖z‖)` (`1` at `z = 0`, supported in
`‖z‖ ≤ 1/(n+1)`). -/
def smallBump (n : ℕ) (z : Fin r → ℂ) : ℝ := max 0 (1 - ((n : ℝ) + 1) * ‖z‖)

theorem continuous_smallBump (n : ℕ) : Continuous (smallBump (r := r) n) :=
  continuous_const.max (continuous_const.sub (continuous_const.mul continuous_norm))

theorem smallBump_nonneg (n : ℕ) (z : Fin r → ℂ) : 0 ≤ smallBump n z := le_max_left _ _

theorem smallBump_le_one (n : ℕ) (z : Fin r → ℂ) : smallBump n z ≤ 1 := by
  unfold smallBump
  refine max_le zero_le_one ?_
  have : 0 ≤ ((n : ℝ) + 1) * ‖z‖ := by positivity
  linarith

theorem smallBump_zero (n : ℕ) : smallBump n (0 : Fin r → ℂ) = 1 := by
  simp [smallBump]

theorem smallBump_eq_zero {n : ℕ} {z : Fin r → ℂ} (hz : 1 ≤ ((n : ℝ) + 1) * ‖z‖) :
    smallBump n z = 0 := by
  unfold smallBump
  exact max_eq_left (by linarith)

/-- **The small-mark count test** `(x, z) ↦ t·β_R(x)·max(0, 1 - (n+1)‖z‖)`. -/
def smallMarkTest (R t : ℝ) (n : ℕ) : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ :=
  ⟨⟨fun p => t * cutBump R p.1 * smallBump n p.2,
    (continuous_const.mul ((continuous_cutBump R).comp continuous_fst)).mul
      ((continuous_smallBump n).comp continuous_snd)⟩, by
    refine HasCompactSupport.intro ((isCompact_Icc (a := -(R + 1)) (b := R + 1)).prod
      (isCompact_closedBall (0 : Fin r → ℂ) 1)) fun p hp => ?_
    simp only [Set.mem_prod, Set.mem_Icc, Metric.mem_closedBall, dist_zero_right, not_and_or,
      not_le] at hp
    show t * cutBump R p.1 * smallBump n p.2 = 0
    rcases hp with (h | h) | h
    · rw [cutBump_eq_zero (by linarith [neg_abs_le p.1]), mul_zero, zero_mul]
    · rw [cutBump_eq_zero (by linarith [le_abs_self p.1]), mul_zero, zero_mul]
    · rw [smallBump_eq_zero, mul_zero]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      nlinarith⟩

theorem smallMarkTest_apply (R t : ℝ) (n : ℕ) (p : ℝ × (Fin r → ℂ)) :
    smallMarkTest R t n p = t * cutBump R p.1 * smallBump n p.2 := rfl

theorem smallMarkTest_nonneg (R : ℝ) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (p : ℝ × (Fin r → ℂ)) :
    0 ≤ smallMarkTest R t n p :=
  mul_nonneg (mul_nonneg ht (cutBump_nonneg R _)) (smallBump_nonneg n _)

theorem smallMarkTest_zero (R t : ℝ) (n : ℕ) (x : ℝ) :
    smallMarkTest R t n (x, (0 : Fin r → ℂ)) = t * cutBump R x := by
  rw [smallMarkTest_apply, smallBump_zero, mul_one]

/-!
## The limit side
-/

/-- `1 - L(f) ≤ ∫∫ f` for the decorated sine Laplace functional (`1 - e^{-y} ≤ y` and the
intensity formula). -/
theorem one_sub_decoratedSineLaplace_le (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ)
    (hf : ∀ p, 0 ≤ f p) :
    1 - decoratedSineLaplace r f ≤ ∫ x, ∫ g, f (x, g) ∂circularVectorLaw (Fin r) := by
  obtain ⟨Ω', _, P', Ξ, hΞ⟩ := BlockBand.Critical.DecoratedSine.exists_isDecoratedSineProcess r
  have := hΞ.prob
  set Y : Ω' → ℝ := fun ω => ∫ p, f p ∂(Ξ ω).measure
  have hYm : Measurable Y := (BlockBand.Endpoints.measurable_coordinate f).comp hΞ.measurable
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => integral_nonneg fun p => hf p
  have hI := lintegral_coordinate_of_decoratedSine hΞ f hf
  have hI0 : 0 ≤ ∫ x, ∫ g, f (x, g) ∂circularVectorLaw (Fin r) :=
    integral_nonneg fun x => integral_nonneg fun g => hf _
  rw [← hΞ.laplace f hf]
  have hexp : Integrable (fun ω => Real.exp (-Y ω)) P' := by
    refine Integrable.of_bound (Real.measurable_exp.comp hYm.neg).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (hY0 ω))
  have h1 : 1 - ∫ ω, Real.exp (-Y ω) ∂P' = ∫ ω, (1 - Real.exp (-Y ω)) ∂P' := by
    rw [integral_sub (integrable_const 1) hexp]; simp
  have hnn : 0 ≤ᵐ[P'] fun ω => 1 - Real.exp (-Y ω) := Eventually.of_forall fun ω => by
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 (hY0 ω)); simp only [Pi.zero_apply]; linarith
  have hms : AEStronglyMeasurable (fun ω => 1 - Real.exp (-Y ω)) P' :=
    (measurable_const.sub (Real.measurable_exp.comp hYm.neg)).aestronglyMeasurable
  rw [h1, integral_eq_lintegral_of_nonneg_ae hnn hms]
  calc (∫⁻ ω, ENNReal.ofReal (1 - Real.exp (-Y ω)) ∂P').toReal
      ≤ (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P').toReal := by
        rw [hI]
        refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
        rw [← hI]
        refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
        have := Real.add_one_le_exp (-Y ω)
        linarith
    _ = ∫ x, ∫ g, f (x, g) ∂circularVectorLaw (Fin r) := by
        rw [hI, ENNReal.toReal_ofReal hI0]

theorem integral_cutBump_nonneg (R : ℝ) : 0 ≤ ∫ x, cutBump R x :=
  integral_nonneg fun x => cutBump_nonneg R x

/-- The intensity of the small-mark test factorizes. -/
theorem intensity_smallMarkTest (R t : ℝ) (n : ℕ) :
    ∫ x, ∫ g, smallMarkTest R t n (x, g) ∂circularVectorLaw (Fin r) =
      t * (∫ x, cutBump R x) * ∫ g, smallBump n g ∂circularVectorLaw (Fin r) := by
  simp only [smallMarkTest_apply]
  simp_rw [integral_const_mul]
  rw [integral_mul_const, integral_const_mul]

/-- **Small marks are rare** in the limit: `∫ max(0, 1 - (n+1)‖g‖) dγ_r → 0` (`r ≥ 1`). -/
theorem tendsto_integral_smallBump (hr : 0 < r) :
    Tendsto (fun n : ℕ => ∫ g, smallBump n g ∂circularVectorLaw (Fin r)) atTop (𝓝 0) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have h0 := BlockBand.Coarea.ProjectiveHaar.circularVectorLaw_ae_ne_zero (Fin r)
  have hlim : (∫ _g, (0 : ℝ) ∂circularVectorLaw (Fin r)) = 0 := integral_zero _ _
  rw [← hlim]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (continuous_smallBump n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun g => ?_) ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (smallBump_nonneg n g)]
    exact smallBump_le_one n g
  · filter_upwards [h0] with g hg
    have hpos : 0 < ‖g‖ := norm_pos_iff.2 hg
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / ‖g‖)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n₀] with n hn
    symm
    refine smallBump_eq_zero ?_
    have h1 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : 1 / ‖g‖ * ‖g‖ = 1 := by field_simp
    nlinarith

/-- **The small-mark test is nearly invisible in the limit**: for `r ≥ 1`, `R`, `t ≥ 0` and
`η > 0` there is `n` with `1 - L(t β_R(x) max(0, 1 - (n+1)‖z‖)) ≤ η`. -/
theorem exists_smallMarkTest (hr : 0 < r) (R : ℝ) {t : ℝ} (ht : 0 ≤ t) {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, 1 - decoratedSineLaplace r (smallMarkTest (r := r) R t n) ≤ η := by
  set c := t * ∫ x, cutBump R x
  have hc : 0 ≤ c := mul_nonneg ht (integral_cutBump_nonneg R)
  have hT : Tendsto (fun n : ℕ => c * ∫ g, smallBump n g ∂circularVectorLaw (Fin r)) atTop
      (𝓝 (c * 0)) := (tendsto_integral_smallBump hr).const_mul c
  rw [mul_zero] at hT
  obtain ⟨n, hn⟩ := (hT.eventually (gt_mem_nhds hη)).exists
  refine ⟨n, (one_sub_decoratedSineLaplace_le _ (smallMarkTest_nonneg R ht n)).trans ?_⟩
  rw [intensity_smallMarkTest]
  exact hn.le

end BlockBand.Critical.MatrixClosing.Poles
