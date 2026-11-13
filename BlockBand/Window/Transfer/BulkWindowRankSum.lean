module

public import BlockBand.Window.Transfer.OriginalVarianceRankLocalization

/-!
# The bulk window rank sum

For a state `Y` independent of a centred Gaussian scalar `t` of variance `σ²`: the finite bulk
transfer `Σ_{α∈s} E[...] ≤ C (a/√n) ε^{1-1/q}` and the full window bound
`𝒱 ≤ C (a/√n) ε^{1-1/q} + outsideWindowRemainder`, the latter an observable- and
`ε`-independent expectation over the complementary ranks.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BlockBand.Window.Transfer

/-- The scalar-kernel prefactor at the physical scalar variance, using `Nσ = √(cn)`. -/
theorem original_scalar_prefactor (p : BlockBand.Parameters) (rho : ℝ) (hrho : 0 < rho) :
    scalarKernelPrefactor ((p.N : ℝ) * rho) (originalScalarSigma p) =
      (rho * Real.sqrt (2 * Real.pi) * Real.sqrt p.c)⁻¹ / Real.sqrt (p.n : ℝ) := by
  have hc := p.c_pos
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hsigma := originalScalarSigma_pos p
  unfold scalarKernelPrefactor
  rw [show ((p.N : ℝ) * rho) * originalScalarSigma p * Real.sqrt (2 * Real.pi) =
    rho * Real.sqrt (2 * Real.pi) * ((p.N : ℝ) * originalScalarSigma p) by ring]
  rw [dimension_mul_originalScalarSigma, Real.sqrt_mul hc.le]
  field_simp

/-- The bulk-transfer constant, independent of `a`, `ε`, the observables and the spectra; it
depends on `b` only through `c = 1 - 2b`. -/
noncomputable def bulkTransferConstant (p : BlockBand.Parameters) (q rho beta D M : ℝ) : ℝ :=
  2 * ((2 : ℝ) ^ q * (cappedRankConstant p q rho beta D M) ^ (1 / q) / (q - 1)) *
    (rho * Real.sqrt (2 * Real.pi) * Real.sqrt p.c)⁻¹

variable {Omega State : Type*} [MeasurableSpace Omega] [MeasurableSpace State]

/-- Finite bulk-window transfer from the Gaussian law of the scalar and the `L^q` rank moments:
`Σ_{α∈s} E[A_α w-convolution] ≤ C (a/√n) ε^{1-1/q}`. The centre may be any real number,
for instance `N F_sc(E)`. -/
theorem actual_bulk_window_rank_sum
    (p : BlockBand.Parameters) (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Y : Omega → State) (t : Omega → ℝ) (hY : Measurable Y) (ht : Measurable t)
    (hlaw : HasLaw t (gaussianReal 0 (scalarVariance (originalScalarSigma p))) mu)
    (hind : IndepFun Y t mu)
    (A X : Fin p.N → State → ℝ) (hA : ∀ i, Measurable (A i)) (hX : ∀ i, Measurable (X i))
    (hA0 : ∀ i y, 0 ≤ A i y) (hA1 : ∀ i y, A i y ≤ 1)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ x, w x = 1) (hw0 : ∀ x, 0 ≤ w x)
    (s : Finset (Fin p.N)) (e : Fin p.N → ℝ)
    (center q rho beta D a M E epsilon : ℝ) (hq : 1 < q) (hrho : 0 < rho)
    (hbeta : 0 < beta) (hD : 0 ≤ D) (ha : Real.sqrt (p.n : ℝ) ≤ a)
    (ha1 : 1 ≤ a) (hM : 0 ≤ M) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsupp : ∀ x, w x ≠ 0 → |x| ≤ M)
    (hsep : ∀ i ∈ s, beta * |rankCoordinate i - center| / (p.N : ℝ) ≤ |e i - E|)
    (hLp : ∀ i ∈ s, eLpNorm (fun y => X i y - e i) (ENNReal.ofReal q) (mu.map Y) ≤
      ENNReal.ofReal (D * a / (p.N : ℝ)))
    (hmean : ∀ i ∈ s, (∫ omega, A i (Y omega) ∂mu) ≤ epsilon) :
    Integrable (fun omega => ∑ i ∈ s, A i (Y omega) *
      w ((p.N : ℝ) * rho * (X i (Y omega) + t omega - E))) mu ∧
    (∫ omega, ∑ i ∈ s, A i (Y omega) *
      w ((p.N : ℝ) * rho * (X i (Y omega) + t omega - E)) ∂mu) ≤
      bulkTransferConstant p q rho beta D M * (a / Real.sqrt (p.n : ℝ)) *
        epsilon ^ (1 - 1 / q) := by
  have hq0 : 0 < q := by linarith
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hsigma := originalScalarSigma_pos p
  have hc := p.c_pos
  have hC : 0 ≤ cappedRankConstant p q rho beta D M := by
    unfold cappedRankConstant largeRankConstant fixedRankCutoff
    positivity
  have hper (i : Fin p.N) (hi : i ∈ s) :=
    original_variance_correlated_capped_rank_tail p mu Y t hY ht hlaw hind
      (A i) (X i) (hA i) (hX i) (hA0 i) (hA1 i) w hw hcompact hunit hw0
      q rho beta D a M E (e i) |rankCoordinate i - center| epsilon
      hq0 hrho hbeta hD ha ha1 hM (abs_nonneg _) hepsilon1 hsupp
      (hsep i hi) (hLp i hi) (hmean i hi)
  have hInt := integrable_finsetSum s (fun i hi => (hper i hi).1)
  refine ⟨hInt, ?_⟩
  calc
    _ = ∑ i ∈ s, ∫ omega, A i (Y omega) *
        w ((p.N : ℝ) * rho * (X i (Y omega) + t omega - E)) ∂mu :=
      integral_finsetSum s (fun i hi => (hper i hi).1)
    _ ≤ ∑ i ∈ s, scalarKernelPrefactor ((p.N : ℝ) * rho) (originalScalarSigma p) *
        min epsilon (cappedRankConstant p q rho beta D M *
          (a / (1 + |rankCoordinate i - center|)) ^ q) :=
      Finset.sum_le_sum fun i hi => (hper i hi).2
    _ = scalarKernelPrefactor ((p.N : ℝ) * rho) (originalScalarSigma p) *
        ∑ i ∈ s, min epsilon (cappedRankConstant p q rho beta D M *
          (a / (1 + |rankCoordinate i - center|)) ^ q) := by rw [Finset.mul_sum]
    _ ≤ scalarKernelPrefactor ((p.N : ℝ) * rho) (originalScalarSigma p) *
        (2 * (((2 : ℝ) ^ q * (cappedRankConstant p q rho beta D M) ^ (1 / q) /
          (q - 1)) * a * epsilon ^ (1 - 1 / q))) :=
      mul_le_mul_of_nonneg_left
        (actual_rank_tail_sum_bound s center q a epsilon (cappedRankConstant p q rho beta D M)
          hq ha1 hepsilon hepsilon1 hC) (by unfold scalarKernelPrefactor; positivity)
    _ = _ := by
      rw [original_scalar_prefactor p rho hrho]
      unfold bulkTransferConstant
      ring

/-- Integrability of the scalar convolution kernel under the marginal law, uniformly in the rank
location. -/
theorem integrable_original_scalar_kernel (p : BlockBand.Parameters)
    (nu : Measure State) [IsProbabilityMeasure nu] (X : State → ℝ) (hX : Measurable X)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ x, w x = 1) (hw0 : ∀ x, 0 ≤ w x)
    (rho M E : ℝ) (hrho : 0 < rho) (hsupp : ∀ x, w x ≠ 0 → |x| ≤ M) :
    Integrable (fun y => scalarConvolution w ((p.N : ℝ) * rho) E (originalScalarSigma p) (X y)) nu := by
  let B := scalarKernelPrefactor ((p.N : ℝ) * rho) (originalScalarSigma p)
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hk := fun y => scalarConvolution_uniform w hw hcompact hunit hw0
    ((p.N : ℝ) * rho) E (originalScalarSigma p) M (X y)
    (mul_pos hN hrho) (originalScalarSigma_pos p) hsupp
  apply (integrable_const B).mono'
    (((measurable_scalarConvolution w hw.measurable _ _ _).comp hX).aestronglyMeasurable)
  filter_upwards with y
  simpa only [Function.comp_apply, B, Real.norm_eq_abs, abs_of_nonneg (hk y).1] using (hk y).2

/-- The outside-margin remainder: the expected scalar convolution summed over the complementary
ranks, under the traceless marginal; it is independent of the observables and of `ε`. -/
noncomputable def outsideWindowRemainder (p : BlockBand.Parameters) (nu : Measure State)
    (X : Fin p.N → State → ℝ) (w : ℝ → ℝ) (rho E : ℝ) (s : Finset (Fin p.N)) : ℝ :=
  ∫ y, ∑ i ∈ sᶜ, scalarConvolution w ((p.N : ℝ) * rho) E (originalScalarSigma p) (X i y) ∂nu

/-- The outside remainder is integrable and nonnegative. -/
theorem outside_window_remainder_integrable_nonneg (p : BlockBand.Parameters)
    (nu : Measure State) [IsProbabilityMeasure nu]
    (X : Fin p.N → State → ℝ) (hX : ∀ i, Measurable (X i))
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ x, w x = 1) (hw0 : ∀ x, 0 ≤ w x)
    (rho M E : ℝ) (hrho : 0 < rho) (hsupp : ∀ x, w x ≠ 0 → |x| ≤ M)
    (s : Finset (Fin p.N)) :
    Integrable (fun y => ∑ i ∈ sᶜ,
      scalarConvolution w ((p.N : ℝ) * rho) E (originalScalarSigma p) (X i y)) nu ∧
    0 ≤ outsideWindowRemainder p nu X w rho E s := by
  refine ⟨integrable_finsetSum sᶜ (fun i hi =>
    integrable_original_scalar_kernel p nu (X i) (hX i) w hw hcompact hunit hw0 rho M E hrho hsupp), ?_⟩
  apply integral_nonneg
  intro y
  apply Finset.sum_nonneg
  intro i hi
  exact integral_nonneg fun t => hw0 _

/-- The full finite window is bounded by the bulk transfer plus the outside remainder, which is
independent of `A` and `ε`. Only bulk ranks need the rank moment and observable mean inputs. The
decay of the remainder along critical sequences is `critical_actual_outside_remainder_tendsto`. -/
theorem full_window_bulk_plus_outside_remainder
    (p : BlockBand.Parameters) (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Y : Omega → State) (t : Omega → ℝ) (hY : Measurable Y) (ht : Measurable t)
    (hlaw : HasLaw t (gaussianReal 0 (scalarVariance (originalScalarSigma p))) mu)
    (hind : IndepFun Y t mu)
    (A X : Fin p.N → State → ℝ) (hA : ∀ i, Measurable (A i)) (hX : ∀ i, Measurable (X i))
    (hA0 : ∀ i y, 0 ≤ A i y) (hA1 : ∀ i y, A i y ≤ 1)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ x, w x = 1) (hw0 : ∀ x, 0 ≤ w x)
    (s : Finset (Fin p.N)) (e : Fin p.N → ℝ)
    (center q rho beta D a M E epsilon : ℝ) (hq : 1 < q) (hrho : 0 < rho)
    (hbeta : 0 < beta) (hD : 0 ≤ D) (ha : Real.sqrt (p.n : ℝ) ≤ a)
    (ha1 : 1 ≤ a) (hM : 0 ≤ M) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsupp : ∀ x, w x ≠ 0 → |x| ≤ M)
    (hsep : ∀ i ∈ s, beta * |rankCoordinate i - center| / (p.N : ℝ) ≤ |e i - E|)
    (hLp : ∀ i ∈ s, eLpNorm (fun y => X i y - e i) (ENNReal.ofReal q) (mu.map Y) ≤
      ENNReal.ofReal (D * a / (p.N : ℝ)))
    (hmean : ∀ i ∈ s, (∫ omega, A i (Y omega) ∂mu) ≤ epsilon) :
    Integrable (fun omega => ∑ i : Fin p.N, A i (Y omega) *
      w ((p.N : ℝ) * rho * (X i (Y omega) + t omega - E))) mu ∧
    (∫ omega, ∑ i : Fin p.N, A i (Y omega) *
      w ((p.N : ℝ) * rho * (X i (Y omega) + t omega - E)) ∂mu) ≤
      bulkTransferConstant p q rho beta D M * (a / Real.sqrt (p.n : ℝ)) *
        epsilon ^ (1 - 1 / q) + outsideWindowRemainder p (mu.map Y) X w rho E s := by
  classical
  let : IsProbabilityMeasure (mu.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hIdentity (i : Fin p.N) := scalar_first_window_integral mu Y t hY ht
    (originalScalarSigma p) hlaw hind (A i) (X i) (hA i) (hX i) (hA0 i) (hA1 i)
    w hw hcompact ((p.N : ℝ) * rho) E
  have hKernelInt (i : Fin p.N) := integrable_original_scalar_kernel p (mu.map Y)
    (X i) (hX i) w hw hcompact hunit hw0 rho M E hrho hsupp
  have hBulk := actual_bulk_window_rank_sum p mu Y t hY ht hlaw hind A X hA hX hA0 hA1
    w hw hcompact hunit hw0 s e center q rho beta D a M E epsilon hq hrho hbeta hD
    ha ha1 hM hepsilon hepsilon1 hsupp hsep hLp hmean
  have hOut : (∫ omega, ∑ i ∈ sᶜ, A i (Y omega) *
      w ((p.N : ℝ) * rho * (X i (Y omega) + t omega - E)) ∂mu) ≤
      outsideWindowRemainder p (mu.map Y) X w rho E s := by
    calc
      _ = ∑ i ∈ sᶜ, ∫ omega, A i (Y omega) *
          w ((p.N : ℝ) * rho * (X i (Y omega) + t omega - E)) ∂mu :=
        integral_finsetSum sᶜ (fun i hi => (hIdentity i).1)
      _ = ∑ i ∈ sᶜ, ∫ y, A i y * scalarConvolution w ((p.N : ℝ) * rho)
          E (originalScalarSigma p) (X i y) ∂(mu.map Y) :=
        Finset.sum_congr rfl fun i hi => (hIdentity i).2.2
      _ ≤ ∑ i ∈ sᶜ, ∫ y, scalarConvolution w ((p.N : ℝ) * rho)
          E (originalScalarSigma p) (X i y) ∂(mu.map Y) :=
        Finset.sum_le_sum fun i hi => integral_mono (hIdentity i).2.1 (hKernelInt i) fun y =>
          mul_le_of_le_one_left
            (scalarConvolution_uniform w hw hcompact hunit hw0 ((p.N : ℝ) * rho)
              E (originalScalarSigma p) M (X i y) (mul_pos hN hrho)
              (originalScalarSigma_pos p) hsupp).1 (hA1 i y)
      _ = _ := (integral_finsetSum sᶜ (fun i hi => hKernelInt i)).symm
  have hSplit : (∫ omega, ∑ i : Fin p.N, A i (Y omega) *
      w ((p.N : ℝ) * rho * (X i (Y omega) + t omega - E)) ∂mu) =
      (∫ omega, ∑ i ∈ s, A i (Y omega) *
        w ((p.N : ℝ) * rho * (X i (Y omega) + t omega - E)) ∂mu) +
      (∫ omega, ∑ i ∈ sᶜ, A i (Y omega) *
        w ((p.N : ℝ) * rho * (X i (Y omega) + t omega - E)) ∂mu) := by
    rw [integral_finsetSum Finset.univ (fun i hi => (hIdentity i).1),
      integral_finsetSum s (fun i hi => (hIdentity i).1),
      integral_finsetSum sᶜ (fun i hi => (hIdentity i).1)]
    exact (Finset.sum_add_sum_compl s (fun i => ∫ omega, A i (Y omega) *
      w ((p.N : ℝ) * rho * (X i (Y omega) + t omega - E)) ∂mu)).symm
  refine ⟨integrable_finsetSum Finset.univ (fun i hi => (hIdentity i).1), ?_⟩
  rw [hSplit]
  exact add_le_add hBulk.2 hOut

end BlockBand.Window.Transfer
