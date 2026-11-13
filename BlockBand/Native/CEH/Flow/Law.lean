module

public import BlockBand.Palm.MomentFlow.EventLocal
public import BlockBand.Palm.MomentFlow.BridgeBrownian

/-!
# CEH flow: law transport from a Hermitian Brownian motion to the CEH source

The time-`s` marginal of a Hermitian Brownian motion is the scaled CEH Gaussian source, so events
of `F + G s` have the same probability as the corresponding events of `F + √s W`.

* `map_gueSourceLaw_smul_eq_gueIncrementLaw`: `(gueSourceLaw N).map (√δ • ·.1) =
  gueIncrementLaw N δ`.
* `hasLaw_hermitianBrownian`: `G s ~ gueIncrementLaw N s` under `Q`.
* **`hermitianBrownian_measure_eq`**: for measurable `S`,
  `Q {ω | G s ω ∈ S} = gueSourceLaw N {W | √s • W.1 ∈ S}`.
* `hermitianBrownian_shift_measure_eq`, `hermitianBrownian_deformed_measure_eq`: for every matrix
  `F`, measurable `T`, `gueSourceLaw N {W | F + √s • W.1 ∈ T} = Q {ω | F + G s ω ∈ T}`, and the
  same with CEH's `deformedMatrix (√s) F W` (definitionally `F.1 + √s • W.1`).
* `hermitianBrownian_deformedHermitian_measure_eq`: the same on the Hermitian sample space, for a
  measurable `E ⊆ CEH.SourceHermitian N` and `⟨F.1 + G s ω, _⟩`.
* `hermitianBrownian_isotropicBad_eq`, `hermitianBrownian_averagedBad_eq`: the CEH bad events of
  `ExternalLocalGUE` (`isotropicBadEvent`, `averagedBadEvent`, at `λ = √s`) have
  `gueSourceLaw N`-measure equal to the `Q`-measure of the corresponding events for the resolvent
  `(F + G s ω - z)⁻¹`; measurability is `measurableSet_isotropicBadEvent`,
  `measurableSet_averagedBadEvent` (from `EventLocal`'s `measurableSet_isoBadSet`,
  `measurableSet_avgBadSet`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.Flow
open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.External BlockBand.Coarea.GUELaw
open BlockBand.Palm.MomentFlow
open scoped NNReal ENNReal

variable {N : ℕ}

/-!
## The GUE increment law is `GUE_N(δ/N)` and the scaled CEH source
-/

theorem measurable_hermitianOfCoords' : Measurable (hermitianOfCoords N) := by
  rw [← brownianOfCoords_eq_hermitianOfCoords]; exact measurable_brownianOfCoords

/-- The increment law `gueIncrementLaw N δ` is `GUE_N(δ/N)` (`gueMeasure (Fin N) (δ / N)`). -/
theorem gueIncrementLaw_eq_gueMeasure (δ : ℝ≥0) :
    gueIncrementLaw N δ = gueMeasure (Fin N) (δ / N) := by
  have hfun : hermitianOfCoords N = gueOfCoords N ∘ (fun r => (Real.sqrt N)⁻¹ • r) := by
    rw [← brownianOfCoords_eq_hermitianOfCoords]
    funext r; simp only [Function.comp_apply, brownianOfCoords_eq]
  unfold gueIncrementLaw
  rw [hfun, ← Measure.map_map measurable_gueOfCoords (measurable_const_smul _),
    pi_gaussian_map_smul, gueMeasure_eq_map_coords]
  congr 2
  funext _
  congr 1
  ext
  simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [Real.coe_toNNReal _ (inv_nonneg.2 (Nat.cast_nonneg N))]
  ring

/-- `√δ W` with `W ~ gueSourceLaw N` has law `gueIncrementLaw N δ`. -/
theorem map_gueSourceLaw_smul_eq_gueIncrementLaw (δ : ℝ≥0) :
    (gueSourceLaw N).map (fun W : CEH.SourceHermitian N => ((Real.sqrt δ : ℝ) : ℂ) • W.1) =
      gueIncrementLaw N δ := by
  rw [map_gueSourceLaw_smul δ.coe_nonneg, gueIncrementLaw_eq_gueMeasure]
  congr 1
  ext
  simp [Real.coe_toNNReal _ (div_nonneg δ.coe_nonneg (Nat.cast_nonneg N))]

/-!
## The marginal law of a Hermitian Brownian motion
-/

section Brownian

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}

/-- `G s ~ gueIncrementLaw N s`. -/
theorem hasLaw_hermitianBrownian (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0) :
    HasLaw (G s) (gueIncrementLaw N s) Q := by
  have h := hG.law 0 s zero_le
  simp only [hG.zero, sub_zero, tsub_zero] at h
  exact h

/-- **Law transport.** `Q {G s ∈ S} = gueSourceLaw N {√s W ∈ S}` for measurable `S`. -/
theorem hermitianBrownian_measure_eq (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0)
    {S : Set (Matrix (Fin N) (Fin N) ℂ)} (hS : MeasurableSet S) :
    Q {ω | G s ω ∈ S} =
      gueSourceLaw N {W : CEH.SourceHermitian N | ((Real.sqrt s : ℝ) : ℂ) • W.1 ∈ S} := by
  have hm : Measurable (fun W : CEH.SourceHermitian N => ((Real.sqrt s : ℝ) : ℂ) • W.1) :=
    (measurable_matrix_const_smul _).comp measurable_subtype_coe
  rw [(hasLaw_hermitianBrownian hG s).measure_eq (p := fun K => K ∈ S) hS,
    ← map_gueSourceLaw_smul_eq_gueIncrementLaw, Set.ofPred_mem_eq, Measure.map_apply hm hS]
  rfl

theorem measurable_const_add_matrix (F : Matrix (Fin N) (Fin N) ℂ) :
    Measurable (fun K : Matrix (Fin N) (Fin N) ℂ => F + K) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.add_apply]
  exact measurable_const.add (measurable_matrixEntry i j)

/-- Shifted form: `gueSourceLaw N {F + √s W ∈ T} = Q {F + G s ∈ T}` for measurable `T`. -/
theorem hermitianBrownian_shift_measure_eq (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0)
    (F : Matrix (Fin N) (Fin N) ℂ) {T : Set (Matrix (Fin N) (Fin N) ℂ)} (hT : MeasurableSet T) :
    gueSourceLaw N {W : CEH.SourceHermitian N | F + ((Real.sqrt s : ℝ) : ℂ) • W.1 ∈ T} =
      Q {ω | F + G s ω ∈ T} :=
  (hermitianBrownian_measure_eq hG s (measurable_const_add_matrix F hT)).symm

/-- The same with CEH's `deformedMatrix (√s) F W = F.1 + √s W.1`. -/
theorem hermitianBrownian_deformed_measure_eq (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0)
    (F : CEH.SourceHermitian N) {T : Set (Matrix (Fin N) (Fin N) ℂ)} (hT : MeasurableSet T) :
    gueSourceLaw N {W : CEH.SourceHermitian N | CEH.deformedMatrix (Real.sqrt s) F W ∈ T} =
      Q {ω | F.1 + G s ω ∈ T} :=
  hermitianBrownian_shift_measure_eq hG s F.1 hT

/-- The same on the Hermitian sample space, for a measurable `E ⊆ CEH.SourceHermitian N`. -/
theorem hermitianBrownian_deformedHermitian_measure_eq (hG : IsHermitianBrownian Q 𝓖 N G)
    (s : ℝ≥0) (F : CEH.SourceHermitian N) {E : Set (CEH.SourceHermitian N)}
    (hE : MeasurableSet E) :
    gueSourceLaw N {W | CEH.deformedHermitian (Real.sqrt s) F W ∈ E} =
      Q {ω | (⟨F.1 + G s ω, F.2.add (hG.hermitian s ω)⟩ : CEH.SourceHermitian N) ∈ E} := by
  obtain ⟨T, hT, rfl⟩ := hE
  exact hermitianBrownian_deformed_measure_eq hG s F hT

/-!
## The CEH bad events
-/

theorem measurableSet_isotropicBadEvent {lam : ℝ} {F : CEH.SourceHermitian N}
    (M : CEH.MDEBranch lam F) (x y : Fin N → ℂ) (z : ℂ) (δ : ℝ) :
    MeasurableSet (CEH.isotropicBadEvent M x y z δ) := by
  have hm : Measurable (fun W : CEH.SourceHermitian N => ((lam : ℝ) : ℂ) • W.1) :=
    (measurable_matrix_const_smul _).comp measurable_subtype_coe
  exact hm (measurableSet_isoBadSet F.1 (M.matrix z) x y z
    ((N : ℝ) ^ δ * CEH.isotropicControl (M.matrix z) z x y))

theorem measurableSet_averagedBadEvent {lam : ℝ} {F : CEH.SourceHermitian N}
    (M : CEH.MDEBranch lam F) (B : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (δ : ℝ) :
    MeasurableSet (CEH.averagedBadEvent M B z δ) := by
  have hm : Measurable (fun W : CEH.SourceHermitian N => ((lam : ℝ) : ℂ) • W.1) :=
    (measurable_matrix_const_smul _).comp measurable_subtype_coe
  exact hm (measurableSet_avgBadSet F.1 (M.matrix z) B z
    ((N : ℝ) ^ δ * CEH.averagedControl (M.matrix z) B z))

/-- The CEH isotropic bad event of `F + √s W` has the `Q`-probability of the corresponding
event for `(F + G s - z)⁻¹`. -/
theorem hermitianBrownian_isotropicBad_eq (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0)
    {F : CEH.SourceHermitian N} (M : CEH.MDEBranch (Real.sqrt s) F) (x y : Fin N → ℂ) (z : ℂ)
    (δ : ℝ) :
    gueSourceLaw N (CEH.isotropicBadEvent M x y z δ) =
      Q {ω | (N : ℝ) ^ δ * CEH.isotropicControl (M.matrix z) z x y <
        ‖star x ⬝ᵥ (((F.1 + G s ω - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - M.matrix z) *ᵥ y)‖} :=
  (hermitianBrownian_measure_eq hG s (measurableSet_isoBadSet F.1 (M.matrix z) x y z
    ((N : ℝ) ^ δ * CEH.isotropicControl (M.matrix z) z x y))).symm

/-- The CEH averaged bad event of `F + √s W` has the `Q`-probability of the corresponding
event for `(F + G s - z)⁻¹`. -/
theorem hermitianBrownian_averagedBad_eq (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0)
    {F : CEH.SourceHermitian N} (M : CEH.MDEBranch (Real.sqrt s) F)
    (B : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (δ : ℝ) :
    gueSourceLaw N (CEH.averagedBadEvent M B z δ) =
      Q {ω | (N : ℝ) ^ δ * CEH.averagedControl (M.matrix z) B z <
        ‖CEH.normalizedTrace (((F.1 + G s ω - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
          M.matrix z) * B)‖} :=
  (hermitianBrownian_measure_eq hG s (measurableSet_avgBadSet F.1 (M.matrix z) B z
    ((N : ℝ) ^ δ * CEH.averagedControl (M.matrix z) B z))).symm

end Brownian

end BlockBand.Native.CEH.Flow
