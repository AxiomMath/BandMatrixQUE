module
public import BlockBand.SourceProcess.Stochastic.Levy.CharFun
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.HasLaw
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Lévy's characterization of Brownian motion on arbitrary filtered spaces

Setting: arbitrary filtered probability space `(Ω, 𝓖, Q)`, `Ω : Type u`, raw filtration.

* `IsFiltrationBrownian Q 𝓖 B`: `B` is a `d`-dimensional `𝓖`-Brownian motion: adapted, a.s.
  continuous, `B_0 = 0` a.s., and for `s ≤ t` the increment `B_t - B_s` is independent of `𝓖_s`
  with law `N(0, (t-s) I_d) = Measure.pi (fun _ => gaussianReal 0 (t - s))`.
* `map_restrict_increment`: for a continuous semimartingale `M` with characteristics `(0, I)`,
  `s ≤ t` and `A ∈ 𝓖_s`, the image of `Q|_A` under `M_t - M_s` is `Q(A) · N(0,(t-s)I)`
  (uniqueness of characteristic functions, `Measure.ext_of_charFunDual`, fed by
  `setIntegral_cexp_increment`).
* `levy_indep`, `levy_hasLaw`: independence of `M_t - M_s` from `𝓖_s` and its Gaussian law.
* **`IsLevyMartingale.isFiltrationBrownian` (Lévy's characterization)**: if `M` is progressive,
  a.s. continuous, `M_0 = 0` a.s., and `M^i`, `M^i M^j - δ_ij t` have `𝓖`-martingale
  modifications, then `M` is a `𝓖`-Brownian motion.
-/

namespace BlockBand.SourceProcess.Stochastic.Levy
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

universe u

variable {d : ℕ}

/-- The centred Gaussian law `N(0, v I_d)` on `ℝ^d`. -/
def gaussPi (d : ℕ) (v : ℝ≥0) : Measure (Fin d → ℝ) := Measure.pi fun _ => gaussianReal 0 v

instance (v : ℝ≥0) : IsProbabilityMeasure (gaussPi d v) := by unfold gaussPi; infer_instance

/-- A continuous linear functional on `ℝ^d` in coordinates. -/
theorem strongDual_apply_eq (L : StrongDual ℝ (Fin d → ℝ)) (x : Fin d → ℝ) :
    L x = pairing (fun i => L (Pi.single i 1)) x := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  simp [map_sum, pairing, mul_comm]

/-- Characteristic function of `N(0, v I_d)`. -/
theorem integral_cexp_gaussPi (w : Fin d → ℝ) (v : ℝ≥0) :
    ∫ x, Complex.exp ((pairing w x : ℂ) * Complex.I) ∂gaussPi d v =
      ((Real.exp (-(sqNorm w / 2 * (v : ℝ))) : ℝ) : ℂ) := by
  have e : ∀ x : Fin d → ℝ, Complex.exp ((pairing w x : ℂ) * Complex.I) =
      ∏ i, Complex.exp (((w i : ℝ) : ℂ) * ((x i : ℝ) : ℂ) * Complex.I) := fun x => by
    rw [← Complex.exp_sum]; congr 1
    simp [pairing, Finset.sum_mul]
  simp_rw [e]
  rw [gaussPi, integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun i (y : ℝ) => Complex.exp (((w i : ℝ) : ℂ) * ((y : ℝ) : ℂ) * Complex.I))]
  simp_rw [← charFun_apply_real, charFun_gaussianReal, ← Complex.exp_sum]
  rw [Complex.ofReal_exp]
  congr 1
  simp [sqNorm, Finset.sum_div, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {M : ℝ≥0 → Ω → Fin d → ℝ}

theorem measurable_increment (hM : ∀ t, StronglyMeasurable[𝓖 t] (M t)) (s t : ℝ≥0) :
    Measurable fun ω => M t ω - M s ω :=
  ((hM t).mono (𝓖.le t)).measurable.sub ((hM s).mono (𝓖.le s)).measurable

/-- **Conditional law of the increment.** For `s ≤ t` and `A ∈ 𝓖_s`,
`(Q|_A) ∘ (M_t - M_s)⁻¹ = Q(A) · N(0, (t-s) I)`. -/
theorem map_restrict_increment
    (hM : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1))
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) :
    (Q.restrict A).map (fun ω => M t ω - M s ω) = Q A • gaussPi d (t - s) := by
  have hm := measurable_increment hM.adapted s t
  have : IsFiniteMeasure (Q A • gaussPi d (t - s)) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]; exact measure_lt_top _ _⟩
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  have hc : Continuous fun x : Fin d → ℝ => Complex.exp ((L x : ℂ) * Complex.I) := by fun_prop
  rw [charFunDual_apply, charFunDual_apply, integral_map hm.aemeasurable hc.aestronglyMeasurable,
    integral_smul_measure]
  obtain ⟨w, hw⟩ : ∃ w : Fin d → ℝ, ∀ x, L x = pairing w x := ⟨_, strongDual_apply_eq L⟩
  simp_rw [hw]
  rw [setIntegral_cexp_increment hM _ hst hA, integral_cexp_gaussPi,
    NNReal.coe_sub hst, Complex.real_smul, Complex.ofReal_mul, Measure.real]

/-- `Q(A ∩ {M_t - M_s ∈ B}) = Q(A) N(0,(t-s)I)(B)` for `A ∈ 𝓖_s`. -/
theorem measure_inter_increment
    (hM : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1))
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓖 s] A)
    {B : Set (Fin d → ℝ)} (hB : MeasurableSet B) :
    Q ((fun ω => M t ω - M s ω) ⁻¹' B ∩ A) = Q A * gaussPi d (t - s) B := by
  have h := congrArg (fun μ : Measure (Fin d → ℝ) => μ B) (map_restrict_increment hM hst hA)
  rwa [Measure.map_apply (measurable_increment hM.adapted s t) hB,
    Measure.restrict_apply (measurable_increment hM.adapted s t hB), Measure.smul_apply,
    smul_eq_mul] at h

/-- **Gaussian law of the increments.** -/
theorem levy_hasLaw (hM : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1))
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => M t ω - M s ω) (gaussPi d (t - s)) Q := by
  refine ⟨(measurable_increment hM.adapted s t).aemeasurable, ?_⟩
  have h := map_restrict_increment hM hst (MeasurableSet.univ (m := 𝓖 s))
  rwa [Measure.restrict_univ, measure_univ, one_smul] at h

/-- **Independence of the increments from the past.** -/
theorem levy_indep (hM : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1))
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => M t ω - M s ω) inferInstance) (𝓖 s) Q := by
  rw [Indep_iff]
  rintro _ A ⟨B, hB, rfl⟩ hA
  rw [measure_inter_increment hM hst hA hB, ← (levy_hasLaw hM hst).map_eq,
    Measure.map_apply (measurable_increment hM.adapted s t) hB, mul_comm]

/-- **`d`-dimensional Brownian motion with respect to a filtration** (raw filtration, a.s.
continuous paths): adapted, `B_0 = 0` a.s., increments `B_t - B_s` independent of `𝓖_s` with
law `N(0, (t-s) I_d)`. -/
structure IsFiltrationBrownian (Q : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (B : ℝ≥0 → Ω → Fin d → ℝ) :
    Prop where
  adapted : ∀ t, StronglyMeasurable[𝓖 t] (B t)
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => B t ω
  zero : ∀ᵐ ω ∂Q, B 0 ω = 0
  indep : ∀ s t, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (𝓖 s) Q
  hasLaw : ∀ s t, s ≤ t → HasLaw (fun ω => B t ω - B s ω) (gaussPi d (t - s)) Q

/-- Lévy for continuous semimartingales: characteristics `(0, I)` and `M_0 = 0` a.s. give a
`𝓖`-Brownian motion. -/
theorem isFiltrationBrownian_of_isContinuousSemimartingale
    (hM : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1))
    (h0 : ∀ᵐ ω ∂Q, M 0 ω = 0) : IsFiltrationBrownian Q 𝓖 M :=
  ⟨hM.adapted, hM.continuous, h0, fun _ _ hst => levy_indep hM hst,
    fun _ _ hst => levy_hasLaw hM hst⟩

/-- **Lévy's characterization of Brownian motion** (arbitrary filtered probability space, raw
filtration, modification form). -/
theorem IsLevyMartingale.isFiltrationBrownian (hM : IsLevyMartingale Q 𝓖 M) :
    IsFiltrationBrownian Q 𝓖 M :=
  isFiltrationBrownian_of_isContinuousSemimartingale hM.isContinuousSemimartingale hM.zero

/-- Lévy's characterization, conditional characteristic function form. -/
theorem IsLevyMartingale.condExp_cexp (hM : IsLevyMartingale Q 𝓖 M) (u : Fin d → ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Q[fun ω => Complex.exp ((pairing u (M t ω - M s ω) : ℂ) * Complex.I) | 𝓖 s] =ᵐ[Q]
      fun _ => ((Real.exp (-(sqNorm u / 2 * ((t : ℝ) - s))) : ℝ) : ℂ) :=
  condExp_cexp_increment hM.isContinuousSemimartingale u hst

end BlockBand.SourceProcess.Stochastic.Levy
