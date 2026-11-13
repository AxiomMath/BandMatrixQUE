module

public import BlockBand.SourceProcess.Stochastic.Angular.Path

/-!
# Complex angular martingale problem: random tests from deterministic ones

`simpleSpectrumAngular_of_deterministic : DeterministicAngular N r → SimpleSpectrumAngular N r`.
Let `m = 𝓖_s ⊔ σ(λ(H_{s+v}) : v ≥ 0)` and `J ω = jet (f ω)` on the ball of radius
`frameBound V` (which contains every angular array of unit vectors). `J` is `m`-measurable
(`measurable_jet`) into a separable metric space, so `SimpleFunc.approxOn` gives `m`-simple
approximants **with values in the range of `J`**: each value is the jet of a test
`f ω_c`, which is `C²`, phase invariant and obeys the uniform bounds. On each fiber the
approximating variable is the variable of the deterministic test `f ω_c`, so it integrates to
`0` (`DeterministicAngular`). Pathwise, the variable is Lipschitz in the jet
(`abs_coordVar_jet_sub_le`) and uniformly bounded (`abs_coordVar_test_le`), so dominated
convergence passes to the limit.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory Filter Topology Matrix Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

variable {N r : ℕ}

theorem angVar_congr {Ω : Type*} (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (ev : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ)
    (s : ℝ≥0) (V : Matrix (Fin N) (Fin r) ℂ) (n : ℕ) {f f' : Ω → AngularArray N r → ℝ} {ω : Ω}
    (h : f ω = f' ω) (u : ℝ≥0) : angVar F G ev s V n f u ω = angVar F G ev s V n f' u ω := by
  simp only [angVar, stoppedProcess, h]

theorem condSigma_le {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}
    (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F) (s : ℝ≥0) :
    𝓖 s ⊔ eigenPathSigma N F G s ≤ (inferInstance : MeasurableSpace Ω) := by
  refine sup_le (𝓖.le s) (iSup_le fun v => ?_)
  exact ((measurable_pi_iff.2 fun i => measurable_dysonEigenvalue i).comp
    ((measurable_hermBM_add hG hF (s + v)).mono (𝓖.le (s + v)) le_rfl)).comap_le

/-- **Random tests from deterministic tests.** -/
theorem simpleSpectrumAngular_of_deterministic (hD : DeterministicAngular N r) :
    SimpleSpectrumAngular N r := by
  intro Ω _ Q _ 𝓖 G F hG hF hFh ev hev s hsimple V n hn f hf hfp hfm hfb u
  classical
  have hmle := condSigma_le hG hF s
  set R := frameBound V
  set J : Ω → C(Kb N r R, JetSp N) := fun ω => jet (hf ω) R
  have hJ : Measurable[𝓖 s ⊔ eigenPathSigma N F G s] J := measurable_jet hf hfm R
  obtain ⟨ω₀, -⟩ := hsimple.exists
  obtain ⟨ap, T, hT, hap, hfib, htend⟩ := @exists_approx_range Ω _ (𝓖 s ⊔ eigenPathSigma N F G s) _ _ _ _ J hJ ω₀
  let pick : C(Kb N r R, JetSp N) → Ω := fun c => if h : c ∈ range J then h.choose else ω₀
  have hpick : ∀ c ∈ range J, J (pick c) = c := fun c hc => by
    simp only [pick, hc, dite_true]
    exact hc.choose_spec
  -- uniform constants
  obtain ⟨C, hC⟩ := hfb R
  have hR : 0 ≤ R := frameBound_nonneg V
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC ω₀ 0 (by simpa using hR)).1
  set L := 2 + (u : ℝ) * (N * N * (1 / (N * (1 / (n : ℝ)) ^ 2)))
  set B := 2 * C + (u : ℝ) * (N * N * (1 / (N * (1 / (n : ℝ)) ^ 2)) * (2 * C * (R ^ 2 + R)))
  -- the approximating variables
  set E : ℕ → Ω → ℝ := fun k ω => angVar F G ev s V n (fun _ => f (pick (ap k ω))) u ω
  have hErep : ∀ k, E k = fun ω => ∑ c ∈ T k,
      ((ap k) ⁻¹' {c}).indicator (angVar F G ev s V n (fun _ => f (pick c)) u) ω := by
    intro k; funext ω
    rw [Finset.sum_eq_single (ap k ω)]
    · rw [indicator_of_mem (by simp)]
    · intro c _ hc
      exact indicator_of_notMem (by simpa [eq_comm] using hc) _
    · intro h; exact absurd (hT k ω) h
  have hDc := fun c => hD Ω Q 𝓖 G F hG hF hFh ev hev s hsimple V n hn (f (pick c)) (hf _)
    (hfp _) u
  have hEint : ∀ k, Integrable (E k) Q := fun k => by
    rw [hErep k]
    exact integrable_finsetSum _ fun c _ => (hDc c).1.indicator (hmle _ (hfib k c))
  have hE0 : ∀ k, ∫ ω, E k ω ∂Q = 0 := fun k => by
    rw [hErep k, integral_finsetSum _ fun c _ => (hDc c).1.indicator (hmle _ (hfib k c))]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [integral_indicator (hmle _ (hfib k c))]
    exact (hDc c).2 _ (hfib k c)
  -- pathwise estimates
  have hbd : ∀ k, ∀ᵐ ω ∂Q, ‖E k ω‖ ≤ B := fun k => by
    filter_upwards [hsimple] with ω hω
    show ‖angVar F G ev s V n (fun _ => f (pick (ap k ω))) u ω‖ ≤ B
    rw [Real.norm_eq_abs, angVar_eq_coordVar_of hG hFh hev V (f := fun _ => f (pick (ap k ω)))
      (hfp _) hω u]
    exact abs_coordVar_test_le hG hFh hω V hn hC0 (fun Z hZ => hC _ Z hZ) u
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun k => E k ω) atTop
      (𝓝 (angVar F G ev s V n f u ω)) := by
    filter_upwards [hsimple] with ω hω
    have ht := htend ω
    rw [tendsto_iff_dist_tendsto_zero] at ht ⊢
    have hL : 0 ≤ L := by positivity
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) (by simpa using ht.const_mul L)
    rw [Real.dist_eq]
    simp only [E]
    rw [angVar_eq_coordVar_of hG hFh hev V (f := fun _ => f (pick (ap k ω))) (hfp _) hω u,
      angVar_eq_coordVar_of hG hFh hev V (hfp ω) hω u]
    have h1 := abs_coordVar_jet_sub_le hG hFh hω V (hf (pick (ap k ω))) (hf ω)
      (hfp _) (hfp ω) hn u
    have h2 : jet (hf (pick (ap k ω))) R = ap k ω := hpick _ (hap k ω)
    rw [h2] at h1
    exact h1
  -- dominated convergence
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => B)
    (fun k => (hEint k).aestronglyMeasurable) (integrable_const B) hbd hlim
  have hmeas : AEStronglyMeasurable (angVar F G ev s V n f u) Q :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hEint k).aestronglyMeasurable) hlim
  refine ⟨Integrable.of_bound hmeas B ?_, ?_⟩
  · filter_upwards [hsimple] with ω hω
    rw [Real.norm_eq_abs, angVar_eq_coordVar_of hG hFh hev V (hfp ω) hω u]
    exact abs_coordVar_test_le hG hFh hω V hn hC0 (fun Z hZ => hC ω Z hZ) u
  · simp only [hE0] at hDCT
    exact tendsto_nhds_unique hDCT tendsto_const_nhds

end BlockBand.SourceProcess.Stochastic.ComplexAngular
