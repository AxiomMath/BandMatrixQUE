module

public import BlockBand.SourceProcess.Stochastic.Angular.MainDiag

/-!
# Complex angular contract: the degenerate size `N = 0`

The proposition `GenericConditioning N` is **false for `N = 0`**
(`not_genericConditioning_zero`). With `N = 0` the coordinates live in `ℝ^0`: `φ` is constant
along every path, `Δφ = 0 = 2·0·A` places no constraint on `A`, and the gap stop is `⊤`. So
`coordVar = -u · A(0)`. With `φ = 0`, `A = 1`, `u = 1` and the one-point probability space this
integrates to `-1 ≠ 0`. The reduction `complexAngularContract_of_diag` therefore has an
unsatisfiable hypothesis `∀ N, GenericConditioning N`.

The contract holds trivially at `N = 0` (`complexAngularMartingaleProblem_zero`, empty
generator, subsingleton arrays), so `complexAngularContract_of_pos` needs `GenericConditioning N`
only for `0 < N`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

theorem subsingleton_matrix_zero : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) :=
  ⟨fun _ _ => Matrix.ext fun i => i.elim0⟩

attribute [local instance] subsingleton_matrix_zero

/-- The zero process is a Hermitian Brownian motion of size `0` on the one-point space. -/
theorem isHermitianBrownian_zero_size :
    IsHermitianBrownian (Measure.dirac ()) (Filtration.const ℝ≥0 (⊤ : MeasurableSpace Unit) le_rfl) 0
      (fun _ _ => 0) where
  adapted _ := measurable_const
  continuous _ := continuous_const
  hermitian _ _ := isHermitian_zero
  zero _ := rfl
  indep s t _ := by
    simp only [sub_self, MeasurableSpace.comap_const]
    exact indep_bot_left _
  law s t _ := by
    refine ⟨measurable_const.aemeasurable, ?_⟩
    have : IsProbabilityMeasure (gueIncrementLaw 0 (t - s)) := by
      unfold gueIncrementLaw; infer_instance
    ext S hS
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hSu : S = univ := eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
      subst hSu
      simp

/-- **`GenericConditioning 0` is false.** -/
theorem not_genericConditioning_zero : ¬ GenericConditioning 0 := by
  intro h
  have key := (h Unit (Measure.dirac ()) (Filtration.const ℝ≥0 ⊤ le_rfl) (fun _ _ => 0) (fun _ => 0)
    isHermitianBrownian_zero_size measurable_const (fun _ => isHermitian_zero) 0
    (ae_of_all _ fun _ _ i => i.elim0) 1 one_pos (fun _ => 0) (fun _ => 1) measurable_const
    (fun _ _ => contDiffAt_const) measurable_const continuousOn_const
    (fun _ _ => by simp) (fun _ _ i => i.elim0) ⟨0, fun _ => by simp⟩
    ⟨1, fun _ _ _ => by simp⟩ 1).2 univ MeasurableSet.univ
  have hσ : gapStop 0 (fun t (ω : Unit) => (0 : Matrix (Fin 0) (Fin 0) ℂ) + 0) 0 1 =
      fun _ => ⊤ := by
    funext ω
    simp only [gapStop]
    refine iInf_eq_top.2 fun u => iInf_eq_top.2 fun hu => ?_
    obtain ⟨i, -⟩ := hu
    exact i.elim0
  rw [Measure.restrict_univ, integral_dirac] at key
  simp only [coordVar, hσ, Dyson.stoppedProcess_top, sub_self, integral_const, smul_eq_mul,
    mul_one, zero_sub, neg_eq_zero, measureReal_restrict_apply_univ, Real.volume_real_Ioc,
    NNReal.coe_one, sub_zero] at key
  norm_num at key

/-- The contract at `N = 0` (subsingleton arrays, empty generator). -/
theorem complexAngularMartingaleProblem_zero (r : ℕ) : ComplexAngularMartingaleProblem 0 r := by
  intro Ω _ Q _ 𝓖 G F hG hF hFh ev hev s V n hn f hf hfp hfm hfb u
  have e : stoppedProcess (fun v ω =>
      f ω (angularArray V (ev (F ω + G (s + v) ω))) -
        f ω (angularArray V (ev (F ω + G (s + 0) ω))) -
      ∫ w in Set.Ioc (0 : ℝ) v, complexAngularGenerator 0 r
        (dysonEigenvalue 0 (F ω + G (s + w.toNNReal) ω)) (f ω)
        (angularArray V (ev (F ω + G (s + w.toNNReal) ω))))
      (gapStop 0 (fun t ω => F ω + G t ω) s n) u = fun _ => 0 := by
    funext ω
    simp only [stoppedProcess, complexAngularGenerator, Finset.univ_eq_empty,
      Finset.sum_empty, mul_zero, integral_zero, sub_zero]
    rw [Subsingleton.elim (angularArray V (ev (F ω + G (s + _) ω)))
      (angularArray V (ev (F ω + G (s + 0) ω))), sub_self]
  show Integrable _ Q ∧ ∫ ω, _ ∂Q = 0
  rw [e]
  exact ⟨integrable_zero _ _ _, by simp⟩

/-- **The contract from `GenericConditioning` in positive size.** -/
theorem complexAngularContract_of_pos (hC : ∀ N, 0 < N → GenericConditioning N) :
    ComplexAngularContract := by
  refine ⟨fun N r => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact complexAngularMartingaleProblem_zero r
  · exact complexAngularMartingaleProblem_of_simple (simpleSpectrumAngular_of_deterministic
      (deterministicAngular_of (arrayLaplacian N r) (hC N hN)))

end BlockBand.SourceProcess.Stochastic.ComplexAngular
