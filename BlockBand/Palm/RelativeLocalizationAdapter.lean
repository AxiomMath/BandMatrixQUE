module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Internal.Contracts.Transmission
public import BlockBand.Coarea.GUELaw

/-!
# Relative localization: `flowLaw` as a Hermitian Brownian motion

* `flowFiltration N` : the old-state/all-coordinate-past filtration `commonWienerFiltration`
  (raw, unaugmented);
* `flowBM N t ω = hermitianBrownian ω.2 t - hermitianBrownian ω.2 0`;
* `flowInit F ω = F + (ω.1 + ω.1ᴴ)/2 + hermitianBrownian ω.2 0`.

Proved: `flowBM_isHermitianBrownian` (for every `a`, under `flowLaw N a`, for the raw
filtration), `measurable_flowInit` (`𝓖_0`), `flowInit_isHermitian` (every sample, for
Hermitian `F`), and `flowMatrix_eq` : whenever `ω.1` is Hermitian (a `flowLaw`-a.s. event,
`ae_fst_isHermitian`), `flowMatrix F a ω σ = flowInit F ω + flowBM N (σ - a) ω` for `σ ≥ a`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open scoped NNReal ComplexConjugate

variable {N : ℕ}

/-- The raw old-state/coordinate-past filtration on the flow sample space. -/
def flowFiltration (N : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FlowSample N)) :=
  commonWienerFiltration (Matrix (Fin N) (Fin N) ℂ) ((Fin N × Fin N) × Fin 2)

/-- The Hermitian Brownian motion started at `0`. -/
def flowBM (N : ℕ) (t : ℝ≥0) (ω : FlowSample N) : Matrix (Fin N) (Fin N) ℂ :=
  hermitianBrownian ω.2 (t : ℝ) - hermitianBrownian ω.2 0

/-- The initial matrix `F + (G_a + G_aᴴ)/2 + B(0)` (equal to `F + G_a` when `G_a` is Hermitian
and the noise starts at `0`). -/
def flowInit (F : Matrix (Fin N) (Fin N) ℂ) (ω : FlowSample N) : Matrix (Fin N) (Fin N) ℂ :=
  F + ((1 / 2 : ℂ) • (ω.1 + ω.1ᴴ)) + hermitianBrownian ω.2 0

/-- The scalar identity `(√(2N))⁻¹ (1/√2) = 1/(2√N)`. -/
theorem rl_scalar (N : ℕ) :
    ((Real.sqrt (2 * N))⁻¹ : ℂ) * (1 / (Real.sqrt 2 : ℂ)) = ((1 / (2 * Real.sqrt N) : ℝ) : ℂ) := by
  have h2 : Real.sqrt (2 * N) = Real.sqrt 2 * Real.sqrt N :=
    Real.sqrt_mul (by norm_num) _
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2' : Real.sqrt 2 ≠ 0 := by positivity
  rw [h2]
  push_cast
  rcases (Real.sqrt_nonneg (N : ℝ)).lt_or_eq with hN | hN
  · have : (Real.sqrt N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast hs2'
    field_simp
    have : ((Real.sqrt 2 : ℝ) : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by exact_mod_cast hs2
    linear_combination (-1 : ℂ) * this
  · rw [← hN]; simp

/-- Increments of `hermitianBrownian` in real coordinates (`hermitianOfCoords`). -/
theorem hermitianBrownian_sub_eq (B : FlowNoise N) (t s : ℝ≥0) :
    hermitianBrownian B (t : ℝ) - hermitianBrownian B (s : ℝ) =
      hermitianOfCoords N (fun q => B q t - B q s) := by
  ext a b
  simp only [hermitianBrownian, hermitianOfCoords, Real.toNNReal_coe, Matrix.sub_apply,
    Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
    smul_eq_mul, circularBrownianCoordinates, Complex.ofReal_sub, RCLike.star_def, map_add,
    map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_sub]
  have := rl_scalar N
  linear_combination
    ((B ((a, b), 0) t : ℂ) - B ((a, b), 0) s + ((B ((a, b), 1) t : ℂ) - B ((a, b), 1) s) *
      Complex.I + (((B ((b, a), 0) t : ℂ) - B ((b, a), 0) s) -
        ((B ((b, a), 1) t : ℂ) - B ((b, a), 1) s) * Complex.I)) * this

theorem rl_measurable_hermitianOfCoords : Measurable (hermitianOfCoords N) := by
  apply Measurable.of_eval_matrix
  intro a b
  simp only [hermitianOfCoords, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, RCLike.star_def]
  fun_prop

theorem rl_measurable_wienerValue (t : ℝ≥0) :
    Measurable (fun B : FlowNoise N => fun q => B q t) :=
  Measurable.of_eval fun q => (ContinuousMap.measurable_eval t).comp (measurable_pi_apply q)

theorem rl_measurable_hermitianBrownian (t : ℝ) :
    Measurable (fun B : FlowNoise N => hermitianBrownian B t) := by
  apply Measurable.of_eval_matrix
  intro a b
  simp only [hermitianBrownian, Matrix.of_apply, circularBrownianCoordinates]
  have := fun q => (ContinuousMap.measurable_eval (Real.toNNReal t)).comp
    (measurable_pi_apply (X := fun _ : (Fin N × Fin N) × Fin 2 => CanonicalWienerPath) q)
  fun_prop

theorem rl_continuous_hermitianOfCoords : Continuous (hermitianOfCoords N) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [hermitianOfCoords, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, RCLike.star_def]
  fun_prop

/-- Values of the noise at times `≤ t` are `𝓖_t`-measurable functions of the sample. -/
theorem measurable_noise_le {t s : ℝ≥0} (hst : s ≤ t) :
    Measurable[flowFiltration N t] (fun ω : FlowSample N => fun q => ω.2 q s) := by
  change @Measurable _ _ (MeasurableSpace.comap
    (fun x : FlowSample N => (x.1, commonWienerPast t x.2)) _) _ _
  have hev : Measurable (fun z : Matrix (Fin N) (Fin N) ℂ ×
      (((Fin N × Fin N) × Fin 2) → Set.Iic t → ℝ) => fun q => z.2 q ⟨s, hst⟩) :=
    Measurable.of_eval fun q => (measurable_pi_apply (⟨s, hst⟩ : Set.Iic t)).comp
      ((measurable_pi_apply q).comp measurable_snd)
  exact hev.comp (comap_measurable _)

theorem measurable_fst_zero :
    Measurable[flowFiltration N 0] (fun ω : FlowSample N => ω.1) := by
  change @Measurable _ _ (MeasurableSpace.comap
    (fun x : FlowSample N => (x.1, commonWienerPast 0 x.2)) _) _ _
  exact (comap_measurable (fun x : FlowSample N => (x.1, commonWienerPast 0 x.2))).fst

theorem flowBM_eq_coords (t : ℝ≥0) (ω : FlowSample N) :
    flowBM N t ω = hermitianOfCoords N (fun q => ω.2 q t - ω.2 q 0) := by
  rw [flowBM, ← hermitianBrownian_sub_eq]; rfl

theorem flowBM_sub_eq (t s : ℝ≥0) (ω : FlowSample N) :
    flowBM N t ω - flowBM N s ω = hermitianOfCoords N (fun q => ω.2 q t - ω.2 q s) := by
  rw [flowBM, flowBM, ← hermitianBrownian_sub_eq]; abel

theorem hermitianOfCoords_isHermitian (r : ((Fin N × Fin N) × Fin 2) → ℝ) :
    (hermitianOfCoords N r).IsHermitian := by
  unfold hermitianOfCoords
  simp only
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

/-- Under `flowLaw N a` and the raw filtration `flowFiltration N`, `flowBM N` is a Hermitian
Brownian motion (`IsHermitianBrownian`). -/
theorem flowBM_isHermitianBrownian (a : ℝ) :
    IsHermitianBrownian (flowLaw N a) (flowFiltration N) N (flowBM N) where
  adapted t := by
    have h := (rl_measurable_hermitianOfCoords (N := N)).comp
      ((measurable_noise_le (N := N) (le_refl t)).sub (measurable_noise_le (N := N) (zero_le (a := t))))
    have : flowBM N t = hermitianOfCoords N ∘ fun ω : FlowSample N => fun q => ω.2 q t - ω.2 q 0 :=
      funext fun ω => flowBM_eq_coords t ω
    rw [this]; exact h
  continuous ω := by
    have : (fun t => flowBM N t ω) =
        fun t => hermitianOfCoords N (fun q => ω.2 q t - ω.2 q 0) :=
      funext fun t => flowBM_eq_coords t ω
    rw [this]
    refine rl_continuous_hermitianOfCoords.comp (continuous_pi fun q => ?_)
    exact ((ω.2 q).continuous.sub continuous_const)
  hermitian t ω := by rw [flowBM_eq_coords]; exact hermitianOfCoords_isHermitian _
  zero ω := by simp [flowBM]
  indep s t hst := by
    have h := (IndepFun_iff_Indep _ _ _).mp (commonWienerFuture_independent_old_past
      (κ := (Fin N × Fin N) × Fin 2) (gueMeasure (Fin N) (Real.toNNReal (a / N))) s)
    refine indep_of_indep_of_le_left h ?_
    set Φ : (((Fin N × Fin N) × Fin 2) → ℝ≥0 → ℝ) → Matrix (Fin N) (Fin N) ℂ :=
      fun f => hermitianOfCoords N (fun q => f q (t - s)) with hΦ
    have hΦm : Measurable Φ := rl_measurable_hermitianOfCoords.comp
      (Measurable.of_eval fun q => (measurable_pi_apply (t - s)).comp (measurable_pi_apply q))
    have heq : (fun ω : FlowSample N => flowBM N t ω - flowBM N s ω) =
        Φ ∘ fun x : FlowSample N => commonWienerFuture s x.2 := by
      funext ω
      simp only [Function.comp, hΦ, commonWienerFuture, add_tsub_cancel_of_le hst]
      exact flowBM_sub_eq t s ω
    rw [heq]
    exact (hΦm.comp (comap_measurable _)).comap_le
  law s t hst := by
    have h := hasLaw_commonRealBrownian_increment (κ := (Fin N × Fin N) × Fin 2)
      (gueMeasure (Fin N) (Real.toNNReal (a / N))) s t
    have hd : nndist t s = t - s := by
      rw [NNReal.nndist_eq, max_eq_left]
      rw [tsub_eq_zero_of_le hst]; exact zero_le (a := t - s)
    rw [hd] at h
    have h2 := (hasLaw_map (rl_measurable_hermitianOfCoords (N := N)).aemeasurable).comp h
    refine h2.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Function.comp, commonRealBrownian]
    exact flowBM_sub_eq t s ω

/-- `hermitianBrownian` as a function of the coordinate values. -/
def rlBrownianOfCoords (N : ℕ) (r : ((Fin N × Fin N) × Fin 2) → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => ((Real.sqrt (2 * N))⁻¹ : ℂ) *
    (circularBrownianCoordinates r (a, b) + conj (circularBrownianCoordinates r (b, a)))

theorem hermitianBrownian_eq_rlCoords (B : FlowNoise N) (t : ℝ) :
    hermitianBrownian B t = rlBrownianOfCoords N (fun q => B q (Real.toNNReal t)) := rfl

/-- The initial matrix is `𝓖_0`-measurable. -/
theorem measurable_flowInit (F : Matrix (Fin N) (Fin N) ℂ) :
    Measurable[flowFiltration N 0] (flowInit F) := by
  set Ψ : Matrix (Fin N) (Fin N) ℂ × (((Fin N × Fin N) × Fin 2) → ℝ) → Matrix (Fin N) (Fin N) ℂ :=
    fun p => F + ((1 / 2 : ℂ) • (p.1 + p.1ᴴ)) + rlBrownianOfCoords N p.2 with hΨ
  have hΨm : Measurable Ψ := by
    apply Measurable.of_eval_matrix
    intro a b
    simp only [hΨ, Matrix.add_apply, Matrix.smul_apply, Matrix.conjTranspose_apply,
      smul_eq_mul, RCLike.star_def, rlBrownianOfCoords, Matrix.of_apply,
      circularBrownianCoordinates]
    have h1 : ∀ i j : Fin N, Measurable fun p : Matrix (Fin N) (Fin N) ℂ ×
        (((Fin N × Fin N) × Fin 2) → ℝ) => p.1 i j :=
      fun i j => measurable_fst.eval_matrix
    fun_prop
  have hinner : Measurable[flowFiltration N 0]
      (fun ω : FlowSample N => (ω.1, fun q => ω.2 q 0)) :=
    measurable_fst_zero.prodMk (measurable_noise_le (N := N) (le_refl (0 : ℝ≥0)))
  have : flowInit F = Ψ ∘ fun ω : FlowSample N => (ω.1, fun q => ω.2 q 0) := by
    funext ω
    simp only [flowInit, hΨ, Function.comp, hermitianBrownian_eq_rlCoords, Real.toNNReal_zero]
  rw [this]
  exact hΨm.comp hinner

/-- The initial matrix is Hermitian for every sample (for Hermitian `F`). -/
theorem flowInit_isHermitian {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (ω : FlowSample N) : (flowInit F ω).IsHermitian := by
  have h0 : (hermitianBrownian ω.2 0).IsHermitian := by
    ext a b
    simp only [hermitianBrownian, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def,
      map_mul, map_add, Complex.conj_conj, map_inv₀, Complex.conj_ofReal]
    ring
  have hω : ((1 / 2 : ℂ) • (ω.1 + ω.1ᴴ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    congr 1
    simp
  exact (hF.add hω).add h0

/-- The flow sample has a Hermitian initial Gaussian matrix almost surely. -/
theorem ae_fst_isHermitian (a : ℝ) : ∀ᵐ ω ∂flowLaw N a, ω.1.IsHermitian := by
  have h := BlockBand.Coarea.GUELaw.ae_isHermitian_gueMeasure (ι := Fin N)
    (Real.toNNReal (a / N))
  exact (measurePreserving_fst (μ := gueMeasure (Fin N) (Real.toNNReal (a / N)))
    (ν := commonWienerLaw ((Fin N × Fin N) × Fin 2))).quasiMeasurePreserving.ae h

/-- On the a.s. event `ω.1` Hermitian: `flowMatrix F a ω σ = flowInit F ω + flowBM N (σ - a) ω`. -/
theorem flowMatrix_eq (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) {ω : FlowSample N}
    (hω : ω.1.IsHermitian) {σ : ℝ} (hσ : a ≤ σ) :
    flowMatrix F a ω σ = flowInit F ω + flowBM N (Real.toNNReal (σ - a)) ω := by
  have h1 : (1 / 2 : ℂ) • (ω.1 + ω.1ᴴ) = ω.1 := by
    rw [hω.eq]; rw [← two_smul ℂ ω.1, smul_smul]; norm_num
  simp only [flowMatrix, flowInit, flowBM, h1, Real.coe_toNNReal _ (sub_nonneg.mpr hσ)]
  abel

instance flowLaw_isProbabilityMeasure (a : ℝ) : IsProbabilityMeasure (flowLaw N a) := by
  unfold flowLaw; infer_instance

/-- **Non-collision along the flow**: almost surely, `H_σ = flowMatrix F a ω σ` has simple spectrum
for every `σ > a`. -/
theorem flow_simpleSpectrum (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) (a : ℝ) :
    ∀ᵐ ω ∂flowLaw N a, ∀ σ : ℝ, a < σ → HasSimpleSpectrum N (flowMatrix F a ω σ) := by
  have h := (hDBM (FlowSample N) (flowLaw N a) (flowFiltration N) (flowBM N) (flowInit F)
    (flowBM_isHermitianBrownian a) (measurable_flowInit F) (flowInit_isHermitian hF)).1
  filter_upwards [h, ae_fst_isHermitian (N := N) a] with ω hω h1 σ hσ
  rw [flowMatrix_eq F a h1 hσ.le]
  exact hω _ (Real.toNNReal_pos.mpr (sub_pos.mpr hσ))

end BlockBand.Palm.RelativeLocalization
