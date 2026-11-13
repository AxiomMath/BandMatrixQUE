module

public import BlockBand.Critical.RelativeVectors.Angular.CellMean

/-!
# The space-time angular martingale statement from the fixed-time one

`complexAngularMartingaleStatement_of_contract`: `TransmissionAngular.ComplexAngularContract`
(fixed-time random tests) implies `ComplexAngularMartingaleStatement N r` (space-time,
path-parametrized tests) for every `N, r`.

For each `K ≥ 1`, `Λ · S_K` with `S_K = gridSum … K` has mean zero
(`integrable_and_integral_gridSum`). For every sample, `S_K` converges to the stopped space-time
bracket (`tendsto_gridSum`), and `|Λ · S_K| ≤ C_Λ (6C + u |C_t + M_a|)` uniformly, so dominated
convergence gives integrability and mean zero. The premise `0 < s ∨ F a.s. simple` is not used;
`complexAngularMartingale_any_start` states the conclusion for every start time `s ≥ 0` without it.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.Angular

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal

/-- **The space-time angular martingale, every start time.** The conclusion of
`ComplexAngularMartingaleStatement` for every `s ≥ 0`, without the premise
`0 < s ∨ F a.s. simple`. -/
theorem complexAngularMartingale_any_start
    (hC : BlockBand.Internal.Contracts.TransmissionAngular.ComplexAngularContract) (N r : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian)
    (s : ℝ≥0) (V : Matrix (Fin N) (Fin r) ℂ) (n : ℕ) (hn : 0 < n) (T : ℝ≥0)
    (h ht : Ω → ℝ → (Fin N → Fin r → ℂ) → ℝ)
    (hT : IsSpaceTimeAngularTest (BlockBand.Critical.RelativeVectors.eigenPathSigma F G s)
      (gapStop N (fun t ω => F ω + G t ω) s n) T h ht)
    (u : ℝ≥0) (huT : u ≤ T) (Λ : Ω → ℝ)
    (hΛ : Measurable[BlockBand.Critical.RelativeVectors.eigenPathSigma F G s] Λ)
    (hΛb : ∃ C, ∀ ω, |Λ ω| ≤ C) :
    let e : Ω → ℝ := fun ω => Λ ω * (stoppedProcess (fun (v : ℝ≥0) ω =>
        h ω (v : ℝ) (frameArray V (F ω + G (s + v) ω)) - h ω 0 (frameArray V (F ω + G s ω)) -
        ∫ x in Ioc (0 : ℝ) (v : ℝ),
          (ht ω x (frameArray V (F ω + G (s + x.toNNReal) ω)) +
            complexAngularGenerator N r
              (fun i => freshEigenvalue (F ω + G (s + x.toNNReal) ω) i) (h ω x)
              (frameArray V (F ω + G (s + x.toNNReal) ω))))
      (gapStop N (fun t ω => F ω + G t ω) s n) u ω)
    Integrable e Q ∧ ∫ ω, e ω ∂Q = 0 := by
  intro e
  have hH : ∀ t ω, (F ω + G t ω).IsHermitian := fun t ω => (hFh ω).add (hG.hermitian t ω)
  set σ := gapStop N (fun t ω => F ω + G t ω) s n
  set target : Ω → ℝ := fun ω => h ω (stopTime σ u ω) (arrPath F G V s ω (stopTime σ u ω)) -
    h ω 0 (arrPath F G V s ω 0) - ∫ x in Ioc 0 (stopTime σ u ω),
      (ht ω x (arrPath F G V s ω x) + genPath F G V s h ω x x)
  have hpt : ∀ ω, e ω = Λ ω * target ω := by
    intro ω
    simp only [e, target, stoppedProcess, stopTime, arrPath, genPath, Real.toNNReal_coe,
      Real.toNNReal_zero, add_zero]
    rfl
  obtain ⟨C, Ct, Ma, R, hC0, -, hD⟩ := exists_isTelescopeData hG.continuous hH s V hn hT huT
  obtain ⟨CΛ, hCΛ⟩ := hΛb
  set M : ℝ := max CΛ 0 * (6 * C + u * |Ct + Ma|)
  set Fn : ℕ → Ω → ℝ := fun K ω => Λ ω * gridSum (h ω) (genPath F G V s h ω) (arrPath F G V s ω)
    (stopTime σ u ω) u (K + 1)
  have hFn := fun K => integrable_and_integral_gridSum hC hG hF hFh s V hn hT huT hΛ ⟨CΛ, hCΛ⟩
    (Nat.succ_ne_zero K)
  have hbound : ∀ K ω, ‖Fn K ω‖ ≤ M := by
    intro K ω
    have h1 := (hD ω).abs_gridSum_le (Nat.succ_ne_zero K)
    have ht0 := (hD ω).t_nonneg
    have htu := (hD ω).t_le
    have h2 : stopTime σ u ω * (Ct + Ma) ≤ u * |Ct + Ma| :=
      (mul_le_mul_of_nonneg_left (le_abs_self _) ht0).trans
        (mul_le_mul_of_nonneg_right htu (abs_nonneg _))
    simp only [Fn, M, Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ((hCΛ ω).trans (le_max_left _ _)) (h1.trans (by linarith)) (abs_nonneg _)
      (le_max_right _ _)
  have hlim : ∀ ω, Tendsto (fun K => Fn K ω) atTop (𝓝 (Λ ω * target ω)) := fun ω =>
    (((hD ω).tendsto_gridSum).const_mul (Λ ω)).comp (tendsto_add_atTop_nat 1)
  have hmeas : AEStronglyMeasurable (fun ω => Λ ω * target ω) Q :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun K => (hFn K).1.aestronglyMeasurable)
      (ae_of_all _ hlim)
  have hint : Integrable (fun ω => Λ ω * target ω) Q :=
    Integrable.of_bound hmeas M (ae_of_all _ fun ω =>
      le_of_tendsto ((continuous_norm.tendsto _).comp (hlim ω)) (Eventually.of_forall
        fun K => hbound K ω))
  have hzero : ∫ ω, Λ ω * target ω ∂Q = 0 := by
    have hT' := tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun K => (hFn K).1.aestronglyMeasurable) (integrable_const M)
      (fun K => ae_of_all _ (hbound K)) (ae_of_all _ hlim)
    have h0 : (fun K => ∫ ω, Fn K ω ∂Q) = fun _ => (0 : ℝ) := funext fun K => (hFn K).2
    rw [h0] at hT'
    exact tendsto_nhds_unique hT' tendsto_const_nhds
  refine ⟨hint.congr (ae_of_all _ fun ω => (hpt ω).symm), ?_⟩
  rw [← hzero]
  exact integral_congr_ae (ae_of_all _ fun ω => hpt ω)

/-- `ComplexAngularContract` implies `ComplexAngularMartingaleStatement N r`. -/
theorem complexAngularMartingaleStatement_of_contract
    (hC : BlockBand.Internal.Contracts.TransmissionAngular.ComplexAngularContract) (N r : ℕ) :
    BlockBand.Critical.RelativeVectors.ComplexAngularMartingaleStatement N r :=
  fun Ω _ Q _ 𝓖 G F hG hF hFh s _ V n hn T h ht hT u huT Λ hΛ hΛb =>
    complexAngularMartingale_any_start hC N r Ω Q 𝓖 G F hG hF hFh s V n hn T h ht hT u huT Λ hΛ hΛb

end BlockBand.Critical.RelativeVectors.Angular
