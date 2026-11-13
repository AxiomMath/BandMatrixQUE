module

public import BlockBand.Transmission.Generator.Weak
public import BlockBand.Transmission.Generator.Discrete
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Limit-side tools: fdd convergence of `L²`-bounded functionals and Fubini on the limit

* `FddAlong`, `fdd_tendsto`: the fdd clause of `IsPowerTraceLimitAlong` along its subsequence,
  extended (by `tendsto_integral_of_sq_bound`) to continuous functionals with uniformly bounded
  finite-`W` second moments; the limit inherits the bound.
* `cutVec`, `limit_fubini`: for a continuous `H` of the power vector and a bounded test `ψ`,
  `ω ↦ ∫_s^t H(P(u)) du` is integrable and `E[ψ ∫_s^t H(P(u))du] = ∫_s^t E[ψ H(P(u))] du`
  (a jointly measurable version from the a.s. continuous paths).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The fdd convergence of `IsPowerTraceLimitAlong` along a fixed subsequence `σ`. -/
def FddAlong (b : ℝ) (e : ℕ → ℝ) (P : Measure Ω) (Pk : ℕ → ℝ → Ω → ℝ) (σ : ℕ → ℕ) : Prop :=
  ∀ (m : ℕ) (ks : Fin m → ℕ) (ts : Fin m → ℝ),
    (∀ l, 1 ≤ ks l ∧ 0 < ts l) → ∀ Φ : BoundedContinuousFunction (Fin m → ℝ) ℝ,
      Tendsto (fun n => ∫ ω, Φ (fun l => pathPower b (e (σ n)) (σ n) (ks l)
          ⌊((σ n : ℕ) : ℝ) * ts l⌋₊ ω) ∂growthPathLaw (σ n) b) atTop
        (𝓝 (∫ ω, Φ (fun l => Pk (ks l) (ts l) ω) ∂P))

/-- The width-`W` vector at the points `pt l = (k_l, t_l)`. -/
def finVec (b : ℝ) (e : ℕ → ℝ) (W : ℕ) {n : ℕ} (pt : Fin n → ℕ × ℝ) (ω : GrowthPath W) :
    Fin n → ℝ :=
  fun l => pathPower b (e W) W (pt l).1 ⌊(W : ℝ) * (pt l).2⌋₊ ω

/-- The limit vector at the points `pt`. -/
def limVec (Pk : ℕ → ℝ → Ω → ℝ) {n : ℕ} (pt : Fin n → ℕ × ℝ) (ω : Ω) : Fin n → ℝ :=
  fun l => Pk (pt l).1 (pt l).2 ω

theorem measurable_finVec (b : ℝ) (e : ℕ → ℝ) (W : ℕ) {n : ℕ} (pt : Fin n → ℕ × ℝ) :
    Measurable (finVec b e W pt) :=
  measurable_pi_iff.mpr fun _ => measurable_pathPower _ _ _ _

theorem measurable_limVec {Pk : ℕ → ℝ → Ω → ℝ}
    (hmeas : ∀ k, 1 ≤ k → ∀ t, 0 < t → Measurable (Pk k t)) {n : ℕ} (pt : Fin n → ℕ × ℝ)
    (hpt : ∀ l, 1 ≤ (pt l).1 ∧ 0 < (pt l).2) : Measurable (limVec Pk pt) :=
  measurable_pi_iff.mpr fun l => hmeas _ (hpt l).1 _ (hpt l).2

/-- **fdd convergence of an `L²`-bounded continuous functional.** -/
theorem fdd_tendsto {b : ℝ} {e : ℕ → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {Pk : ℕ → ℝ → Ω → ℝ} (hmeas : ∀ k, 1 ≤ k → ∀ t, 0 < t → Measurable (Pk k t))
    {σ : ℕ → ℕ} (hσ : FddAlong b e P Pk σ) {n : ℕ} (pt : Fin n → ℕ × ℝ)
    (hpt : ∀ l, 1 ≤ (pt l).1 ∧ 0 < (pt l).2) {G : (Fin n → ℝ) → ℝ} (hG : Continuous G) {C : ℝ}
    (hC : ∀ᶠ N in atTop, ∫⁻ ω, ‖G (finVec b e (σ N) pt ω)‖ₑ ^ 2 ∂growthPathLaw (σ N) b ≤
      ENNReal.ofReal C) :
    ∫⁻ ω, ‖G (limVec Pk pt ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C ∧
      Tendsto (fun N => ∫ ω, G (finVec b e (σ N) pt ω) ∂growthPathLaw (σ N) b) atTop
        (𝓝 (∫ ω, G (limVec Pk pt ω) ∂P)) :=
  tendsto_integral_of_sq_bound (Ωn := fun N => GrowthPath (σ N))
    (μ := fun N => growthPathLaw (σ N) b) (fun N => measurable_finVec b e (σ N) pt)
    (measurable_limVec hmeas pt hpt) (fun Φ => hσ n (fun l => (pt l).1) (fun l => (pt l).2) hpt Φ)
    hG hC

/-- The power vector of the limit with the unconstrained `k = 0` coordinate set to `0`. -/
def cutVec (Pk : ℕ → ℝ → Ω → ℝ) (u : ℝ) (ω : Ω) : ℕ → ℝ :=
  fun j => if 1 ≤ j then Pk j u ω else 0

theorem measurable_cutVec {Pk : ℕ → ℝ → Ω → ℝ}
    (hmeas : ∀ k, 1 ≤ k → ∀ t, 0 < t → Measurable (Pk k t)) {u : ℝ} (hu : 0 < u) :
    Measurable (cutVec Pk u) := by
  refine measurable_pi_iff.mpr fun j => ?_
  by_cases hj : 1 ≤ j
  · simp only [cutVec, hj, ↓reduceIte]; exact hmeas j hj u hu
  · simp only [cutVec, hj, ↓reduceIte]; exact measurable_const

theorem enorm_le_one_add_sq (x : ℝ) : ‖x‖ₑ ≤ 1 + ‖x‖ₑ ^ 2 := by
  rw [enorm_sq_eq, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (sq_nonneg x)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [abs_nonneg x, sq_abs x]

/-- **Fubini on the limit.** -/
theorem limit_fubini {P : Measure Ω} [IsProbabilityMeasure P] {Pk : ℕ → ℝ → Ω → ℝ}
    (hmeas : ∀ k, 1 ≤ k → ∀ t, 0 < t → Measurable (Pk k t))
    (hcont : ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, ContinuousOn (fun t => Pk k t ω) (Set.Ioi 0))
    {H : (ℕ → ℝ) → ℝ} (hH : Continuous H) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    {ψ : Ω → ℝ} (hψ : Measurable ψ) {B : ℝ} (hB : ∀ ω, |ψ ω| ≤ B) {C : ℝ}
    (hC : ∀ u ∈ Set.Icc s t, ∫⁻ ω, ‖H (cutVec Pk u ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C) :
    Integrable (fun ω => ∫ u in s..t, H (cutVec Pk u ω)) P ∧
      ∫ ω, ψ ω * (∫ u in s..t, H (cutVec Pk u ω)) ∂P =
        ∫ u in s..t, ∫ ω, ψ ω * H (cutVec Pk u ω) ∂P ∧
      IntervalIntegrable (fun u => ∫ ω, ψ ω * H (cutVec Pk u ω) ∂P) volume s t := by
  -- a measurable full-measure set of continuous paths
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, 1 ≤ k → ContinuousOn (fun t => Pk k t ω) (Set.Ioi 0) := by
    refine ae_all_iff.mpr fun k => ?_
    by_cases hk : 1 ≤ k
    · exact (hcont k hk).mono fun ω h _ => h
    · exact Eventually.of_forall fun ω h => absurd h hk
  set S := (toMeasurable P {ω | ¬ ∀ k : ℕ, 1 ≤ k →
    ContinuousOn (fun t => Pk k t ω) (Set.Ioi 0)})ᶜ with hSdef
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hS : ∀ᵐ ω ∂P, ω ∈ S := by
    rw [ae_iff]; simp only [hSdef, Set.mem_compl_iff, not_not, Set.ofPred_mem_eq]
    rw [measure_toMeasurable]; exact ae_iff.mp hall
  have hSgood : ∀ ω ∈ S, ∀ k : ℕ, 1 ≤ k → ContinuousOn (fun t => Pk k t ω) (Set.Ioi 0) := by
    intro ω hω
    by_contra hc
    exact hω (subset_toMeasurable _ _ hc)
  set cl : ℝ → ℝ := fun u => max s (min t u)
  have hcl : Continuous cl := by fun_prop
  have hcl_pos : ∀ u, 0 < cl u := fun u => lt_of_lt_of_le hs (le_max_left _ _)
  have hcl_eq : ∀ u ∈ Set.uIcc s t, cl u = u := by
    intro u hu
    rw [Set.uIcc_of_le hst] at hu
    simp only [cl, min_eq_right hu.2, max_eq_right hu.1]
  set F : ℝ → Ω → ℝ := fun u ω => S.indicator (fun ω => H (cutVec Pk (cl u) ω)) ω
  have hFc : ∀ ω, Continuous fun u => F u ω := by
    intro ω
    by_cases hω : ω ∈ S
    · simp only [F, Set.indicator_of_mem hω]
      refine hH.comp (continuous_pi fun j => ?_)
      by_cases hj : 1 ≤ j
      · simp only [cutVec, hj, ↓reduceIte]
        exact (hSgood ω hω j hj).comp_continuous hcl fun u => hcl_pos u
      · simp only [cutVec, hj, ↓reduceIte]; exact continuous_const
    · simp only [F, Set.indicator_of_notMem hω]; exact continuous_const
  have hFm : ∀ u, Measurable (F u) := fun u =>
    (hH.measurable.comp (measurable_cutVec hmeas (hcl_pos u))).indicator hSm
  have hF2 : Measurable (Function.uncurry F) := measurable_uncurry_of_continuous_of_measurable hFc hFm
  have hFbound : ∀ u ∈ Set.uIoc s t, ∫⁻ ω, ‖F u ω‖ₑ ∂P ≤ 1 + ENNReal.ofReal C := by
    intro u hu
    have hu' : u ∈ Set.Icc s t := by
      rw [Set.uIoc_of_le hst] at hu; exact ⟨hu.1.le, hu.2⟩
    have hcu := hcl_eq u (Set.Icc_subset_uIcc hu')
    calc ∫⁻ ω, ‖F u ω‖ₑ ∂P ≤ ∫⁻ ω, (1 + ‖H (cutVec Pk u ω)‖ₑ ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          simp only [F, hcu]
          by_cases hω : ω ∈ S
          · rw [Set.indicator_of_mem hω]; exact enorm_le_one_add_sq _
          · rw [Set.indicator_of_notMem hω, enorm_zero]; exact zero_le
      _ = 1 + ∫⁻ ω, ‖H (cutVec Pk u ω)‖ₑ ^ 2 ∂P := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ 1 + ENNReal.ofReal C := by gcongr; exact hC u hu'
  -- integrability on the product
  have hint : ∀ {c : Ω → ℝ}, Measurable c → (∀ ω, |c ω| ≤ max B 1) →
      Integrable (Function.uncurry fun u ω => c ω * F u ω)
        ((volume.restrict (Set.uIoc s t)).prod P) := by
    intro c hc hcB
    have hmeas2 : Measurable (Function.uncurry fun u ω => c ω * F u ω) :=
      (hc.comp measurable_snd).mul hF2
    refine ⟨hmeas2.aestronglyMeasurable, ?_⟩
    simp only [HasFiniteIntegral]
    rw [lintegral_prod _ hmeas2.enorm.aemeasurable]
    calc ∫⁻ u, ∫⁻ ω, ‖Function.uncurry (fun u ω => c ω * F u ω) (u, ω)‖ₑ ∂P
          ∂volume.restrict (Set.uIoc s t)
        ≤ ∫⁻ u, ENNReal.ofReal (max B 1) * (1 + ENNReal.ofReal C)
          ∂volume.restrict (Set.uIoc s t) := by
          refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun u hu => ?_)
            |> lintegral_mono_ae
          simp only [Function.uncurry_apply_pair, enorm_mul]
          calc ∫⁻ ω, ‖c ω‖ₑ * ‖F u ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal (max B 1) * ‖F u ω‖ₑ ∂P := by
                refine lintegral_mono fun ω => ?_
                gcongr
                rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (hcB ω)
            _ = ENNReal.ofReal (max B 1) * ∫⁻ ω, ‖F u ω‖ₑ ∂P :=
                lintegral_const_mul _ (hFm u).enorm
            _ ≤ _ := by gcongr; exact hFbound u hu
      _ < ⊤ := by
          rw [lintegral_const]
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, ENNReal.ofReal_lt_top⟩)) ?_
          rw [Measure.restrict_apply_univ, Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  have hψ' : ∀ ω, |ψ ω| ≤ max B 1 := fun ω => (hB ω).trans (le_max_left _ _)
  have h1 := hint hψ hψ'
  have h0 := hint (c := fun _ => (1 : ℝ)) measurable_const fun _ => by simp
  -- identify `F` with the integrand
  have hFω : ∀ᵐ ω ∂P, ∫ u in s..t, F u ω = ∫ u in s..t, H (cutVec Pk u ω) := by
    filter_upwards [hS] with ω hω
    refine intervalIntegral.integral_congr fun u hu => ?_
    simp only [F, Set.indicator_of_mem hω, hcl_eq u hu]
  have hFu : ∀ u ∈ Set.uIcc s t, ∫ ω, ψ ω * F u ω ∂P = ∫ ω, ψ ω * H (cutVec Pk u ω) ∂P := by
    intro u hu
    refine integral_congr_ae ?_
    filter_upwards [hS] with ω hω
    simp only [F, Set.indicator_of_mem hω, hcl_eq u hu]
  constructor
  · have := h0.integral_prod_right
    simp only [Function.uncurry_apply_pair, one_mul] at this
    refine (this.congr ?_)
    filter_upwards [hFω] with ω hω
    rw [← hω, intervalIntegral.integral_of_le hst, Set.uIoc_of_le hst]
  refine ⟨?_, ?_⟩
  · rw [← intervalIntegral.integral_congr hFu, intervalIntegral_integral_swap h1]
    refine integral_congr_ae ?_
    filter_upwards [hFω] with ω hω
    rw [intervalIntegral.integral_const_mul, hω]
  · have h2 := h1.integral_prod_left
    simp only [Function.uncurry_apply_pair] at h2
    rw [intervalIntegrable_iff]
    refine IntegrableOn.congr_fun h2 (fun u hu => hFu u (Set.uIoc_subset_uIcc hu))
      measurableSet_uIoc

end BlockBand.Transmission.Generator
