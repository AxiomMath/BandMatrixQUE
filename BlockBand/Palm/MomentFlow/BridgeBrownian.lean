module

public import BlockBand.Palm.MomentFlow.BridgeRelabel

/-!
# The matrix flow is a Hermitian Brownian motion

*Probability space:* `(FlowSample N, flowLaw N a)` with the natural filtration
`flowFiltration N = commonWienerFiltration` (initial matrix and all Wiener coordinate past).
*Domain:* every `N`, every `a`, every Hermitian `F`.

* `isHermitianBrownian_flowBM`: `G_t := hermitianBrownian ω.2 t - hermitianBrownian ω.2 0` is an
  `IsHermitianBrownian (flowLaw N a) (flowFiltration N) N` (adapted, continuous **for every**
  sample, Hermitian, `G_0 = 0`, increments independent of the past with law
  `gueIncrementLaw N (t - s)`, i.e. `E|G_ij(t) - G_ij(s)|² = (t-s)/N`). The subtraction of the
  time-zero value is needed because a continuous path need not vanish at `0` for every sample;
  under the Wiener law it vanishes almost surely.
* `flowInit`: `F' = F + Herm(ω.1) + hermitianBrownian ω.2 0`, `𝓖_0`-measurable and Hermitian for
  every sample (`measurable_flowInit`, `flowInit_isHermitian`).
* `flowInit_add_flowBM`: `F' + G_t = flowMatrix F a (hermProj ω) (a + t)` for every sample, where
  `hermProj ω = (Herm ω.1, ω.2)`; `hermProj_ae_eq` (`= ω` a.s., since `G_a ~ GUE` is a.s.
  Hermitian), `flowLaw_map_hermProj` (`hermProj` preserves `flowLaw`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess BlockBand.Coarea.GUELaw
open scoped NNReal ComplexConjugate

variable {N : ℕ}

/-- The natural filtration of the flow sample: initial matrix and Wiener coordinate past. -/
abbrev flowFiltration (N : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FlowSample N)) :=
  commonWienerFiltration (Matrix (Fin N) (Fin N) ℂ) ((Fin N × Fin N) × Fin 2)

/-- The Hermitian Brownian motion started at `0`: `G_t = B(t) - B(0)`. -/
def flowBM (N : ℕ) (t : ℝ≥0) (ω : FlowSample N) : Matrix (Fin N) (Fin N) ℂ :=
  hermitianBrownian ω.2 t - hermitianBrownian ω.2 0

/-- Hermitian part `(M + Mᴴ)/2`. -/
def hermPart (M : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := (1 / 2 : ℂ) • (M + Mᴴ)

theorem hermPart_isHermitian (M : Matrix (Fin N) (Fin N) ℂ) : (hermPart M).IsHermitian := by
  unfold hermPart
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

theorem hermPart_of_isHermitian {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.IsHermitian) :
    hermPart M = M := by
  unfold hermPart
  rw [hM.eq, ← two_smul ℂ M, smul_smul]
  norm_num

/-- Projection of the sample onto Hermitian initial matrices. -/
def hermProj (ω : FlowSample N) : FlowSample N := (hermPart ω.1, ω.2)

/-- The `𝓖_0`-measurable Hermitian initial matrix `F' = F + Herm(ω.1) + B(0)`. -/
def flowInit (F : Matrix (Fin N) (Fin N) ℂ) (ω : FlowSample N) : Matrix (Fin N) (Fin N) ℂ :=
  F + hermPart ω.1 + hermitianBrownian ω.2 0

theorem hermitianBrownian_isHermitian (B : FlowNoise N) (t : ℝ) :
    (hermitianBrownian B t).IsHermitian := by
  ext a b
  simp only [hermitianBrownian, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_add,
    Complex.star_def, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem flowInit_isHermitian {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (ω : FlowSample N) : (flowInit F ω).IsHermitian :=
  (hF.add (hermPart_isHermitian _)).add (hermitianBrownian_isHermitian _ _)

theorem flowInit_add_flowBM (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (t : ℝ≥0) : flowInit F ω + flowBM N t ω = flowMatrix F a (hermProj ω) (a + t) := by
  simp only [flowInit, flowBM, flowMatrix, hermProj, add_sub_cancel_left]
  abel

theorem hermProj_eq_of_isHermitian {ω : FlowSample N} (h : ω.1.IsHermitian) : hermProj ω = ω := by
  simp [hermProj, hermPart_of_isHermitian h]

theorem hermProj_ae_eq (a : ℝ) : ∀ᵐ ω ∂flowLaw N a, hermProj ω = ω := by
  have h := ae_isHermitian_gueMeasure (ι := Fin N) (Real.toNNReal (a / N))
  have h' : ∀ᵐ ω ∂flowLaw N a, ω.1.IsHermitian := by
    unfold flowLaw
    exact Measure.quasiMeasurePreserving_fst.ae h
  filter_upwards [h'] with ω hω using hermProj_eq_of_isHermitian hω

theorem measurable_hermPart : Measurable (hermPart (N := N)) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [hermPart, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
    smul_eq_mul]
  have h1 : Measurable (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  have h2 : Measurable (fun M : Matrix (Fin N) (Fin N) ℂ => M j i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply j)
  exact measurable_const.mul (h1.add (Complex.continuous_conj.measurable.comp h2))

theorem measurable_hermProj : Measurable (hermProj (N := N)) :=
  (measurable_hermPart.comp measurable_fst).prodMk measurable_snd

theorem flowLaw_map_hermProj (a : ℝ) : (flowLaw N a).map hermProj = flowLaw N a := by
  rw [Measure.map_congr (hermProj_ae_eq a), Measure.map_id']

/-!
## `G` is an `IsHermitianBrownian`
-/

/-- The real-linear matrix map `Y ↦ (√(2N))⁻¹ (Y + Yᴴ)` on flat complex coordinates. -/
def hermOfFlat (N : ℕ) (Y : (Fin N × Fin N) → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => ((Real.sqrt (2 * N))⁻¹ : ℂ) * (Y (a, b) + conj (Y (b, a)))

theorem measurable_hermOfFlat : Measurable (hermOfFlat N) := by
  apply Measurable.of_eval_matrix
  intro a b
  simp only [hermOfFlat, Matrix.of_apply]
  have h1 : Measurable (fun Y : (Fin N × Fin N) → ℂ => Y (a, b)) := measurable_pi_apply _
  have h2 : Measurable (fun Y : (Fin N × Fin N) → ℂ => Y (b, a)) := measurable_pi_apply _
  exact measurable_const.mul (h1.add (Complex.continuous_conj.measurable.comp h2))

theorem hermOfFlat_sub (Y Z : (Fin N × Fin N) → ℂ) :
    hermOfFlat N Y - hermOfFlat N Z = hermOfFlat N (Y - Z) := by
  ext a b; simp [hermOfFlat, map_sub]; ring

theorem hermitianBrownian_eq_hermOfFlat (ω : FlowSample N) (t : ℝ≥0) :
    hermitianBrownian ω.2 t = hermOfFlat N (commonComplexBrownian t ω) := by
  unfold hermitianBrownian hermOfFlat commonComplexBrownian commonRealBrownian
  rw [Real.toNNReal_coe]

theorem flowBM_sub (t s : ℝ≥0) (ω : FlowSample N) :
    flowBM N t ω - flowBM N s ω =
      hermOfFlat N (commonComplexBrownian t ω - commonComplexBrownian s ω) := by
  simp only [flowBM, hermitianBrownian_eq_hermOfFlat, ← hermOfFlat_sub]
  abel

theorem brownianOfCoords_eq_hermitianOfCoords :
    brownianOfCoords N = hermitianOfCoords N := by
  funext r
  ext a b
  have hs : (Real.sqrt (2 * N))⁻¹ * (Real.sqrt 2)⁻¹ = 1 / (2 * Real.sqrt N) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [← mul_inv, mul_comm (Real.sqrt 2 * Real.sqrt N), ← mul_assoc, h2, one_div]
  have hsC : ((Real.sqrt (2 * N))⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) =
      ((1 / (2 * Real.sqrt N) : ℝ) : ℂ) := by
    rw [← hs]; push_cast; ring
  set w : ℂ := (r ((a, b), 0) : ℂ) + (r ((a, b), 1) : ℂ) * Complex.I
  set w' : ℂ := (r ((b, a), 0) : ℂ) + (r ((b, a), 1) : ℂ) * Complex.I
  have hL : brownianOfCoords N r a b =
      ((Real.sqrt (2 * N))⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) * (w + conj w') := by
    simp only [brownianOfCoords, circularBrownianCoordinates, Matrix.of_apply, map_div₀,
      Complex.conj_ofReal]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hR : hermitianOfCoords N r a b = ((1 / (2 * Real.sqrt N) : ℝ) : ℂ) * (w + conj w') := by
    simp only [hermitianOfCoords, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, smul_eq_mul, Complex.star_def]
    rfl
  rw [hL, hR, hsC]

theorem measurable_flowBM_past (t : ℝ≥0) :
    Measurable (fun z : Matrix (Fin N) (Fin N) ℂ × (((Fin N × Fin N) × Fin 2) → Set.Iic t → ℝ) =>
      brownianOfCoords N (fun q => z.2 q ⟨t, le_rfl⟩) -
        brownianOfCoords N (fun q => z.2 q ⟨0, (zero_le : (0 : ℝ≥0) ≤ t)⟩)) := by
  have h1 : Measurable (fun z : Matrix (Fin N) (Fin N) ℂ ×
      (((Fin N × Fin N) × Fin 2) → Set.Iic t → ℝ) => fun q => z.2 q ⟨t, le_rfl⟩) :=
    Measurable.of_eval fun q => (measurable_pi_apply _).comp ((measurable_pi_apply q).comp measurable_snd)
  have h0 : Measurable (fun z : Matrix (Fin N) (Fin N) ℂ ×
      (((Fin N × Fin N) × Fin 2) → Set.Iic t → ℝ) => fun q => z.2 q ⟨0, (zero_le : (0 : ℝ≥0) ≤ t)⟩) :=
    Measurable.of_eval fun q => (measurable_pi_apply _).comp ((measurable_pi_apply q).comp measurable_snd)
  exact measurable_matrix_sub.comp ((measurable_brownianOfCoords.comp h1).prodMk (measurable_brownianOfCoords.comp h0))

/-- `G_t = B(t) - B(0)` is a Hermitian Brownian motion (`IsHermitianBrownian`) for the natural
filtration under `flowLaw N a`, with `E|G_ij(t)|² = t/N`. -/
theorem isHermitianBrownian_flowBM (a : ℝ) :
    IsHermitianBrownian (flowLaw N a) (flowFiltration N) N (flowBM N) where
  adapted t := by
    change @Measurable _ _ (MeasurableSpace.comap
      (fun x : FlowSample N => (x.1, commonWienerPast t x.2)) _) _ _
    have heq : flowBM N t = (fun z : Matrix (Fin N) (Fin N) ℂ ×
        (((Fin N × Fin N) × Fin 2) → Set.Iic t → ℝ) =>
          brownianOfCoords N (fun q => z.2 q ⟨t, le_rfl⟩) -
            brownianOfCoords N (fun q => z.2 q ⟨0, (zero_le : (0 : ℝ≥0) ≤ t)⟩)) ∘
        (fun x : FlowSample N => (x.1, commonWienerPast t x.2)) := by
      funext ω
      simp [flowBM, hermitianBrownian_eq_coords, commonWienerPast]
    rw [heq]
    exact (measurable_flowBM_past t).comp (comap_measurable _)
  continuous ω := by
    unfold flowBM
    exact ((continuous_hermitianBrownian ω.2).comp NNReal.continuous_coe).sub continuous_const
  hermitian t ω := (hermitianBrownian_isHermitian _ _).sub (hermitianBrownian_isHermitian _ _)
  zero ω := by simp [flowBM]
  indep s t hst := by
    have h := (commonComplexBrownian_future_independent_old_past
      (gueMeasure (Fin N) (Real.toNNReal (a / N))) s).comp
      (φ := fun Y : ℝ≥0 → (Fin N × Fin N) → ℂ => hermOfFlat N (Y (t - s)))
      (ψ := id) (measurable_hermOfFlat.comp (measurable_pi_apply _)) measurable_id
    rw [IndepFun_iff_Indep] at h
    have hfun : ((fun Y : ℝ≥0 → (Fin N × Fin N) → ℂ => hermOfFlat N (Y (t - s))) ∘
        fun x : FlowSample N => fun v => commonComplexBrownian (s + v) x -
          commonComplexBrownian s x) = fun ω => flowBM N t ω - flowBM N s ω := by
      funext ω
      simp only [Function.comp_apply, flowBM_sub, add_tsub_cancel_of_le hst]
    rw [hfun] at h
    exact h
  law s t hst := by
    have h := (hasLaw_map measurable_brownianOfCoords.aemeasurable).comp
      (hasLaw_commonRealBrownian_increment (S := Matrix (Fin N) (Fin N) ℂ)
        (κ := (Fin N × Fin N) × Fin 2) (gueMeasure (Fin N) (Real.toNNReal (a / N))) s t)
    have hd : nndist t s = t - s := by
      rw [NNReal.nndist_eq, max_eq_left (by simp [tsub_eq_zero_of_le hst])]
    rw [hd, brownianOfCoords_eq_hermitianOfCoords] at h
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Function.comp_apply, flowBM, hermitianBrownian_eq_coords, commonRealBrownian,
      Real.toNNReal_coe]
    rw [← brownianOfCoords_eq_hermitianOfCoords]
    ext a b
    simp [brownianOfCoords, circularBrownianCoordinates]
    ring

/-- `F'` is `𝓖_0`-measurable. -/
theorem measurable_flowInit (F : Matrix (Fin N) (Fin N) ℂ) :
    Measurable[flowFiltration N 0] (flowInit F) := by
  change @Measurable _ _ (MeasurableSpace.comap
    (fun x : FlowSample N => (x.1, commonWienerPast 0 x.2)) _) _ _
  have heq : flowInit F = (fun z : Matrix (Fin N) (Fin N) ℂ ×
      (((Fin N × Fin N) × Fin 2) → Set.Iic (0 : ℝ≥0) → ℝ) =>
        F + hermPart z.1 + brownianOfCoords N (fun q => z.2 q ⟨0, le_rfl⟩)) ∘
      (fun x : FlowSample N => (x.1, commonWienerPast 0 x.2)) := by
    funext ω
    simp [flowInit, hermitianBrownian_eq_coords, commonWienerPast]
  rw [heq]
  refine Measurable.comp ?_ (comap_measurable _)
  have h0 : Measurable (fun z : Matrix (Fin N) (Fin N) ℂ ×
      (((Fin N × Fin N) × Fin 2) → Set.Iic (0 : ℝ≥0) → ℝ) => fun q => z.2 q ⟨0, le_rfl⟩) :=
    Measurable.of_eval fun q => (measurable_pi_apply _).comp ((measurable_pi_apply q).comp measurable_snd)
  have hA : Measurable (fun z : Matrix (Fin N) (Fin N) ℂ ×
      (((Fin N × Fin N) × Fin 2) → Set.Iic (0 : ℝ≥0) → ℝ) => hermPart z.1) :=
    measurable_hermPart.comp measurable_fst
  have hB := measurable_brownianOfCoords.comp h0
  apply Measurable.of_eval_matrix
  intro i j
  have e1 : Measurable (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  simp only [Matrix.add_apply]
  exact (measurable_const.add (e1.comp hA)).add (e1.comp hB)

end BlockBand.Palm.MomentFlow
