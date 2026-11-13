module

public import BlockBand.Endpoints.Response.ResponseVarianceDefs
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# The Fourier test on mass profiles: physical and matched-lead sides

The physical Fourier variance `V_{W,m}` is compared with the matched-lead profile through the
physical-lead profile theorem; the cosine square is bounded by the squared complex Fourier mode
for every Gaussian profile.

* `rvFourierTest m ν = ‖ν(e^{2πim·})‖²`, a bounded continuous functional on `𝒫(𝕋)` (weak
  topology), with values in `[0,1]`.
* `rvLeadCos`: the cosine coefficient `Σ_y (h*Y_yh / h*Y^{all}h) cos(2πm k_y/n)` of the
  matched-lead profile (`k_y` the ring block of the position `y`, `n` the ring size; `0` on the
  null event `h*Y^{all}h = 0`).
* `rv_leadCos_sq_le_fourierTest`: for every rotation `J`, `rvLeadCos² ≤ rvFourierTest m (ℛ_J ν^lead)`.
* `rv_fourierTest_leadProfile_eq`: an explicit formula for `rvFourierTest m (ℛ_J ν^lead)` in
  the lead masses (used for joint measurability in the energy, the path and the probe).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal BoundedContinuousFunction

/-!
### The Fourier test
-/

/-- `e^{2πim·}` as a bounded continuous function on the unit torus. -/
def rvFourierBCF (m : ℤ) : Torus →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact (fourier m)

theorem rv_norm_fourier (m : ℤ) (t : Torus) : ‖fourier m t‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

theorem rv_continuous_fourierIntegral (m : ℤ) :
    Continuous (fun ν : MassProfile => ∫ t, fourier m t ∂(ν : Measure Torus)) := by
  rw [continuous_iff_continuousAt]
  intro ν
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ
    (μs := fun ν' : MassProfile => ν') (μ := ν) (F := 𝓝 ν)).1 tendsto_id (rvFourierBCF m)
  exact h

theorem rv_norm_fourierIntegral_le (m : ℤ) (ν : MassProfile) :
    ‖∫ t, fourier m t ∂(ν : Measure Torus)‖ ≤ 1 := by
  calc ‖∫ t, fourier m t ∂(ν : Measure Torus)‖ ≤ ∫ t, ‖fourier m t‖ ∂(ν : Measure Torus) :=
        norm_integral_le_integral_norm _
    _ = 1 := by simp

/-- The Fourier test `ν ↦ ‖ν(e^{2πim·})‖²` on `𝒫(𝕋)`. -/
def rvFourierTest (m : ℤ) : MassProfile →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ν => ‖∫ t, fourier m t ∂(ν : Measure Torus)‖ ^ 2,
      (rv_continuous_fourierIntegral m).norm.pow 2⟩ 1 (fun ν μ => by
      have h1 := rv_norm_fourierIntegral_le m ν
      have h2 := rv_norm_fourierIntegral_le m μ
      have h1' := norm_nonneg (∫ t, fourier m t ∂(ν : Measure Torus))
      have h2' := norm_nonneg (∫ t, fourier m t ∂(μ : Measure Torus))
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]
      constructor <;> nlinarith)

theorem rvFourierTest_apply (m : ℤ) (ν : MassProfile) :
    rvFourierTest m ν = ‖∫ t, fourier m t ∂(ν : Measure Torus)‖ ^ 2 := rfl

theorem rvFourierTest_nonneg (m : ℤ) (ν : MassProfile) : 0 ≤ rvFourierTest m ν := by
  rw [rvFourierTest_apply]; positivity

theorem rvFourierTest_le_one (m : ℤ) (ν : MassProfile) : rvFourierTest m ν ≤ 1 := by
  rw [rvFourierTest_apply]
  have := rv_norm_fourierIntegral_le m ν
  have := norm_nonneg (∫ t, fourier m t ∂(ν : Measure Torus))
  nlinarith

/-!
### The physical side
-/

/-- **`V_{W,m}` is the one-mark statistic of the Fourier test.** -/
theorem rvFourierVariance_eq_physicalOneMark {p : Parameters} (R : FiniteRealization p)
    (E : ℝ) (w : SpectralWeight) (m : ℤ) :
    rvFourierVariance R E w m = physicalOneMark R E w (rvFourierTest m) := by
  have := BlockBand.Model.Construction.massProfile_opensMeasurableSpace
  unfold rvFourierVariance physicalOneMark
  refine integral_congr_ae ?_
  filter_upwards [R.spectral.markedConfig_ae E] with H hH
  rw [hH]
  have hm : Measurable (fun x : MarkedSpectralSpace => w x.1 * rvFourierTest m x.2) :=
    (w.toContinuousMap.continuous.measurable.comp measurable_fst).mul
      ((rvFourierTest m).continuous.measurable.comp measurable_snd)
  rw [integral_finsetSum_measure (fun α _ => integrable_dirac' hm.stronglyMeasurable
    enorm_lt_top)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_dirac' _ _ hm.stronglyMeasurable]
  rfl

/-!
### The matched-lead side
-/

variable {b e : ℝ} {n W : ℕ}

/-- The measure `Σ_y ρ_y δ_{((k_y + J) mod n)/n}` inside `leadProfile` (`ρ_y` the normalized lead
masses, `k_y = leadRingBlock`). -/
def rvLeadMeasure (b e : ℝ) (n W : ℕ) (ω : GrowthPath W) (h : Fin 2 × Fin W → ℂ) (J : ℕ) :
    Measure Torus :=
  ∑ y : Fin (n - 3) ⊕ Fin 2,
    ENNReal.ofReal (leadPositionMass b e W (n - 3) ω h y /
        ∑ y' : Fin (n - 3) ⊕ Fin 2, leadPositionMass b e W (n - 3) ω h y') •
      Measure.dirac (QuotientAddGroup.mk ((((leadRingBlock (n - 3) y + J) % n : ℕ) : ℝ) / n))

theorem rv_dite_elim {α : Type*} {c : Prop} {inst : Decidable c} {t : c → α} {e : ¬c → α}
    {P : α → Prop} (ht : ∀ h, P (t h)) (he : ∀ h, P (e h)) : P (@dite α c inst t e) := by
  cases inst with
  | isTrue h => exact ht h
  | isFalse h => exact he h

theorem rv_leadProfile_cases (b e : ℝ) (n W : ℕ) (ω : GrowthPath W) (h : Fin 2 × Fin W → ℂ)
    (J : ℕ) :
    (IsProbabilityMeasure (rvLeadMeasure b e n W ω h J) ∧
        ((leadProfile b e n W ω h J : MassProfile) : Measure Torus) = rvLeadMeasure b e n W ω h J) ∨
      (¬ IsProbabilityMeasure (rvLeadMeasure b e n W ω h J) ∧
        ((leadProfile b e n W ω h J : MassProfile) : Measure Torus) = Measure.dirac 0) := by
  unfold leadProfile
  dsimp only
  refine rv_dite_elim (P := fun ν : MassProfile =>
      (IsProbabilityMeasure (rvLeadMeasure b e n W ω h J) ∧
        (ν : Measure Torus) = rvLeadMeasure b e n W ω h J) ∨
      (¬ IsProbabilityMeasure (rvLeadMeasure b e n W ω h J) ∧
        (ν : Measure Torus) = Measure.dirac 0)) (fun hμ => ?_) (fun hμ => ?_)
  · exact Or.inl ⟨hμ, rfl⟩
  · exact Or.inr ⟨hμ, rfl⟩

theorem rv_totalLeadMass_nonneg (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    0 ≤ totalLeadMass b e W r x :=
  Finset.sum_nonneg fun _ _ => leadPositionMass_nonneg _ _ _ _ _

theorem rv_isProbabilityMeasure_leadMeasure_iff (ω : GrowthPath W) (h : Fin 2 × Fin W → ℂ)
    (J : ℕ) :
    IsProbabilityMeasure (rvLeadMeasure b e n W ω h J) ↔
      0 < totalLeadMass b e W (n - 3) (ω, h) := by
  have htot := rv_totalLeadMass_nonneg b e W (n - 3) (ω, h)
  have huniv : rvLeadMeasure b e n W ω h J univ =
      ENNReal.ofReal (totalLeadMass b e W (n - 3) (ω, h) /
        totalLeadMass b e W (n - 3) (ω, h)) := by
    rw [rvLeadMeasure, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    have hT : (∑ y', leadPositionMass b e W (n - 3) ω h y') =
        totalLeadMass b e W (n - 3) (ω, h) := rfl
    rw [hT, ← ENNReal.ofReal_sum_of_nonneg (fun y _ => div_nonneg (leadPositionMass_nonneg _ _ _ _ _)
      htot), ← Finset.sum_div]
    rfl
  constructor
  · intro hP
    rcases htot.lt_or_eq with hlt | heq
    · exact hlt
    · have := hP.measure_univ
      rw [huniv, ← heq, div_zero, ENNReal.ofReal_zero] at this
      exact absurd this (by simp)
  · intro hlt
    exact ⟨by rw [huniv, div_self hlt.ne', ENNReal.ofReal_one]⟩

/-- The phase `e^{2πimk/n}`. -/
def rvPhase (m : ℤ) (n k : ℕ) : ℂ := Complex.exp (((2 * Real.pi * m * k / n : ℝ) : ℂ) * Complex.I)

theorem rv_norm_phase (m : ℤ) (n k : ℕ) : ‖rvPhase m n k‖ = 1 := by
  rw [rvPhase, Complex.norm_exp_ofReal_mul_I]

theorem rv_fourier_mk (m : ℤ) (n k : ℕ) :
    fourier m (QuotientAddGroup.mk ((k : ℝ) / n) : Torus) = rvPhase m n k := by
  rw [fourier_coe_apply, rvPhase]
  congr 1
  push_cast
  ring

theorem rv_fourier_rotate (m : ℤ) {n : ℕ} (hn : 0 < n) (k J : ℕ) :
    fourier m (QuotientAddGroup.mk ((((k + J) % n : ℕ) : ℝ) / n) : Torus) =
      rvPhase m n J * rvPhase m n k := by
  rw [rv_fourier_mk, rvPhase, rvPhase, rvPhase, ← Complex.exp_add]
  have hmod : (((k + J) % n : ℕ) : ℝ) = (k : ℝ) + J - n * (((k + J) / n : ℕ) : ℝ) := by
    have := Nat.mod_add_div (k + J) n
    have h' : (((k + J) % n : ℕ) : ℝ) + n * (((k + J) / n : ℕ) : ℝ) = (k : ℝ) + J := by
      exact_mod_cast this
    linarith
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  generalize (k + J) / n = q at hmod ⊢
  have hreal : 2 * Real.pi * m * (((k + J) % n : ℕ) : ℝ) / n =
      2 * Real.pi * m * J / n + 2 * Real.pi * m * k / n - 2 * Real.pi * (m * q) := by
    rw [hmod]; field_simp; ring
  have key : ((2 * Real.pi * m * (((k + J) % n : ℕ) : ℝ) / n : ℝ) : ℂ) * Complex.I =
      (((2 * Real.pi * m * J / n : ℝ) : ℂ) * Complex.I + ((2 * Real.pi * m * k / n : ℝ) : ℂ) *
        Complex.I) + (((-(m * (q : ℤ))) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hreal]
    push_cast
    ring
  rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The complex Fourier coefficient `Σ_y ρ_y e^{2πimk_y/n}` of the (unrotated) matched-lead
profile. -/
def rvLeadFourier (m : ℤ) (b e : ℝ) (n W : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℂ :=
  ∑ y : Fin (n - 3) ⊕ Fin 2,
    ((leadPositionMass b e W (n - 3) x.1 x.2 y / totalLeadMass b e W (n - 3) x : ℝ) : ℂ) *
      rvPhase m n (leadRingBlock (n - 3) y)

/-- The cosine coefficient `Σ_y ρ_y cos(2πmk_y/n)` of the matched-lead profile. -/
def rvLeadCos (m : ℤ) (b e : ℝ) (n W : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  ∑ y : Fin (n - 3) ⊕ Fin 2,
    leadPositionMass b e W (n - 3) x.1 x.2 y / totalLeadMass b e W (n - 3) x *
      Real.cos (2 * Real.pi * m * (leadRingBlock (n - 3) y : ℕ) / n)

theorem rv_leadCos_eq_re (m : ℤ) (b e : ℝ) (n W : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    rvLeadCos m b e n W x = (rvLeadFourier m b e n W x).re := by
  rw [rvLeadCos, rvLeadFourier, Complex.re_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [rvPhase, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem rv_integral_leadMeasure (m : ℤ) (hn : 0 < n) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) (J : ℕ) :
    ∫ t, fourier m t ∂(rvLeadMeasure b e n W ω h J) =
      rvPhase m n J * rvLeadFourier m b e n W (ω, h) := by
  have hc : StronglyMeasurable (fun t : Torus => fourier m t) :=
    (fourier m).continuous.stronglyMeasurable
  have htot := rv_totalLeadMass_nonneg b e W (n - 3) (ω, h)
  have hT : (∑ y', leadPositionMass b e W (n - 3) ω h y') =
      totalLeadMass b e W (n - 3) (ω, h) := rfl
  rw [rvLeadMeasure, hT, integral_finsetSum_measure (fun y _ => (integrable_dirac' hc
    enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)]
  rw [rvLeadFourier, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_smul_measure, integral_dirac' _ _ hc, rv_fourier_rotate m hn,
    ENNReal.toReal_ofReal (div_nonneg (leadPositionMass_nonneg _ _ _ _ _) htot)]
  simp only [Complex.real_smul]
  ring

/-- Explicit form of the Fourier test of the rotated matched-lead profile. -/
theorem rv_fourierTest_leadProfile_eq (m : ℤ) (hn : 0 < n) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) (J : ℕ) :
    rvFourierTest m (leadProfile b e n W ω h J) =
      if 0 < totalLeadMass b e W (n - 3) (ω, h) then ‖rvLeadFourier m b e n W (ω, h)‖ ^ 2
      else 1 := by
  rw [rvFourierTest_apply]
  rcases rv_leadProfile_cases b e n W ω h J with ⟨hP, hL⟩ | ⟨hP, hL⟩
  · simp only [(rv_isProbabilityMeasure_leadMeasure_iff ω h J).1 hP, ↓reduceIte]
    rw [hL,
      rv_integral_leadMeasure m hn, norm_mul, rv_norm_phase, one_mul]
  · simp only [show ¬ 0 < totalLeadMass b e W (n - 3) (ω, h) from
      fun h' => hP ((rv_isProbabilityMeasure_leadMeasure_iff ω h J).2 h'), ↓reduceIte]
    rw [hL,
      integral_dirac' _ _ (fourier m).continuous.stronglyMeasurable, rv_norm_fourier, one_pow]

theorem rv_abs_leadCos_le_one (m : ℤ) (b e : ℝ) (n W : ℕ)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : |rvLeadCos m b e n W x| ≤ 1 := by
  have htot := rv_totalLeadMass_nonneg b e W (n - 3) x
  rw [rvLeadCos]
  calc |∑ y : Fin (n - 3) ⊕ Fin 2, leadPositionMass b e W (n - 3) x.1 x.2 y /
          totalLeadMass b e W (n - 3) x *
            Real.cos (2 * Real.pi * m * (leadRingBlock (n - 3) y : ℕ) / n)|
      ≤ ∑ y : Fin (n - 3) ⊕ Fin 2, leadPositionMass b e W (n - 3) x.1 x.2 y /
          totalLeadMass b e W (n - 3) x := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
        rw [abs_mul, abs_of_nonneg (div_nonneg (leadPositionMass_nonneg _ _ _ _ _) htot)]
        exact mul_le_of_le_one_right (div_nonneg (leadPositionMass_nonneg _ _ _ _ _) htot)
          (Real.abs_cos_le_one _)
    _ ≤ 1 := by
        rw [← Finset.sum_div]
        rcases htot.lt_or_eq with hlt | heq
        · rw [div_le_one hlt]; exact le_of_eq rfl
        · rw [← heq, div_zero]; exact zero_le_one

/-- The cosine square is bounded by the Fourier test of every rotated lead profile. -/
theorem rv_leadCos_sq_le_fourierTest (m : ℤ) (hn : 0 < n) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) (J : ℕ) :
    rvLeadCos m b e n W (ω, h) ^ 2 ≤ rvFourierTest m (leadProfile b e n W ω h J) := by
  rw [rv_fourierTest_leadProfile_eq m hn]
  split_ifs with ht
  · rw [rv_leadCos_eq_re]
    exact sq_le_sq' (abs_le.1 (Complex.abs_re_le_norm _)).1 (abs_le.1 (Complex.abs_re_le_norm _)).2
  · have := rv_abs_leadCos_le_one m b e n W (ω, h)
    nlinarith [abs_nonneg (rvLeadCos m b e n W (ω, h)), sq_abs (rvLeadCos m b e n W (ω, h))]

/-- The averaged lead test of `leadOneMark`: `n⁻¹ Σ_{J<n} Φ(ℛ_J ν^lead)`. -/
def rvLeadAvg (m : ℤ) (b e : ℝ) (n W : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, rvFourierTest m (leadProfile b e n W x.1 x.2 J)

theorem rv_leadCos_sq_le_leadAvg (m : ℤ) (hn : 0 < n) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    rvLeadCos m b e n W x ^ 2 ≤ rvLeadAvg m b e n W x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [rvLeadAvg, le_inv_mul_iff₀ hn']
  calc (n : ℝ) * rvLeadCos m b e n W x ^ 2 = ∑ J ∈ Finset.range n, rvLeadCos m b e n W x ^ 2 := by
        simp
    _ ≤ _ := Finset.sum_le_sum fun J _ => rv_leadCos_sq_le_fourierTest m hn x.1 x.2 J

theorem rv_leadAvg_nonneg (m : ℤ) (b e : ℝ) (n W : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    0 ≤ rvLeadAvg m b e n W x :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ => rvFourierTest_nonneg _ _)

theorem rv_leadAvg_le_one (m : ℤ) (b e : ℝ) (n W : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    rvLeadAvg m b e n W x ≤ 1 := by
  rw [rvLeadAvg]
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [inv_mul_le_iff₀ hn', mul_one]
    calc ∑ J ∈ Finset.range n, rvFourierTest m (leadProfile b e n W x.1 x.2 J)
        ≤ ∑ J ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun J _ => rvFourierTest_le_one _ _
      _ = n := by simp

/-!
### Joint measurability
-/

theorem rv_measurable_totalLeadMass_of (b : ℝ) (W r : ℕ) {α : Type*} [MeasurableSpace α]
    {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)} (he : Measurable e)
    (hx : Measurable x) : Measurable (fun a => totalLeadMass b (e a) W r (x a)) :=
  Finset.measurable_sum _ fun y _ => measurable_leadPositionMass_of b W r y he hx

theorem rv_measurable_leadFourier_of (m : ℤ) (b : ℝ) (n W : ℕ) {α : Type*} [MeasurableSpace α]
    {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)} (he : Measurable e)
    (hx : Measurable x) : Measurable (fun a => rvLeadFourier m b (e a) n W (x a)) := by
  unfold rvLeadFourier
  refine Finset.measurable_sum _ fun y _ => ?_
  exact (Complex.measurable_ofReal.comp ((measurable_leadPositionMass_of b W (n - 3) y he hx).div
    (rv_measurable_totalLeadMass_of b W (n - 3) he hx))).mul_const _

theorem rv_measurable_leadCos_of (m : ℤ) (b : ℝ) (n W : ℕ) {α : Type*} [MeasurableSpace α]
    {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)} (he : Measurable e)
    (hx : Measurable x) : Measurable (fun a => rvLeadCos m b (e a) n W (x a)) := by
  simp_rw [rv_leadCos_eq_re]
  exact Complex.measurable_re.comp (rv_measurable_leadFourier_of m b n W he hx)

theorem rv_measurable_fourierTest_leadProfile_of (m : ℤ) (b : ℝ) {n : ℕ} (hn : 0 < n) (W : ℕ)
    (J : ℕ) {α : Type*} [MeasurableSpace α] {e : α → ℝ}
    {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)} (he : Measurable e) (hx : Measurable x) :
    Measurable (fun a => rvFourierTest m (leadProfile b (e a) n W (x a).1 (x a).2 J)) := by
  simp_rw [rv_fourierTest_leadProfile_eq m hn]
  refine Measurable.ite (measurableSet_lt measurable_const
    (rv_measurable_totalLeadMass_of b W (n - 3) he hx)) ?_ measurable_const
  exact (rv_measurable_leadFourier_of m b n W he hx).norm.pow_const 2

theorem rv_measurable_leadAvg_of (m : ℤ) (b : ℝ) {n : ℕ} (hn : 0 < n) (W : ℕ) {α : Type*}
    [MeasurableSpace α] {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)}
    (he : Measurable e) (hx : Measurable x) :
    Measurable (fun a => rvLeadAvg m b (e a) n W (x a)) :=
  measurable_const.mul (Finset.measurable_sum _ fun J _ =>
    rv_measurable_fourierTest_leadProfile_of m b hn W J he hx)

end BlockBand.Endpoints
