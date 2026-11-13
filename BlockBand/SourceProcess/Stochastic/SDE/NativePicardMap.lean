module
public import BlockBand.SourceProcess.Stochastic.SDE.NativeUnique
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Picard map

`Ω = DriverSample S κ`, `P = driverLaw μ`, horizon `N`, `ν = timeProbMeasure N P`
(`dt ⊗ P` on `(0,N]`), augmented filtration `F_t ∨ N`. Coefficients are globally
`K`-Lipschitz and bounded by `C` (`LipCoeff`); `ξ` is `F_0 ∨ N`-measurable (no
integrability). Picard space: `PicardSpace μ N E = L²(ν; E)` classes with an a.e. raw
predictable representative (`lpMeas`, complete).

For `Z` in the Picard space (thought of as `X − ξ`):
* drift `D_Z(t) = ∫_0^{t∧N} b(ξ + Z_s) ds` (`picardDrift`), continuous and `F_t ∨ N`-adapted;
* noise `M_Z^j = ∫ ℓ_j(σ(ξ + Z)) dW` (`picardNoise`, the continuous stopped integral, `ℓ_j`
  coordinates);
* `Γ Z = D_Z + ∑_j M_Z^j e_j` (`picardMap`), again an element of the Picard space.
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral

/-- Globally Lipschitz, bounded coefficients. -/
structure LipCoeff (κ E : Type*) [NormedAddCommGroup E] where
  b : E → E
  σ : κ → E → E
  K : ℝ≥0
  C : ℝ
  lip_b : LipschitzWith K b
  lip_σ : ∀ a, LipschitzWith K (σ a)
  bd_b : ∀ y, ‖b y‖ ≤ C
  bd_σ : ∀ a y, ‖σ a y‖ ≤ C

section General
variable {α G : Type*} [MeasurableSpace α] {m : Measure α} [NormedAddCommGroup G]

theorem norm_sq_Lp_eq (F : Lp G 2 m) : ‖F‖ ^ 2 = (∫⁻ x, ‖(F : α → G) x‖ₑ ^ 2 ∂m).toReal := by
  rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (Lp.aestronglyMeasurable F)]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.toReal_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem lintegral_enorm_sq_lt_top {f : α → G} (hf : MemLp f 2 m) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m < ⊤ := by
  have := hf.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable] at this
  simp only [ENNReal.toReal_ofNat] at this
  have h2 := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 this
  simpa using h2

theorem memLp_two_of_lintegral {f : α → G} (hf : AEStronglyMeasurable f m)
    (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m < ⊤) : MemLp f 2 m := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  simpa using h.ne

theorem intervalIntegrable_of_bound {f : ℝ → G} (hf : StronglyMeasurable f) {M : ℝ}
    (hM : ∀ s, ‖f s‖ ≤ M) (a b : ℝ) : IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := M)).mono_fun' hf.aestronglyMeasurable
    (Eventually.of_forall fun s => hM s)

end General

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A process with uniformly bounded time-`s` second moments is in `L²(dt ⊗ P)` on `(0,N]`. -/
theorem memLp_two_of_time_bound {N : ℝ≥0} {M : ℝ≥0 → DriverSample S κ → E}
    (hm : AEStronglyMeasurable (fun p : ℝ × DriverSample S κ => M p.1.toNNReal p.2)
      (timeProbMeasure N (driverLaw (κ := κ) μ))) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hb : ∀ s, ∫⁻ x, ‖M s x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ ≤ c) :
    MemLp (fun p : ℝ × DriverSample S κ => M p.1.toNNReal p.2) 2
      (timeProbMeasure N (driverLaw (κ := κ) μ)) := by
  refine memLp_two_of_lintegral hm ?_
  have h2 : AEMeasurable (fun p : ℝ × DriverSample S κ => ‖M p.1.toNNReal p.2‖ₑ ^ 2)
      (timeProbMeasure N (driverLaw (κ := κ) μ)) := hm.enorm.pow_const 2
  unfold timeProbMeasure at h2 ⊢
  rw [lintegral_prod _ h2]
  calc ∫⁻ s in Ioc 0 (N : ℝ), ∫⁻ x, ‖M s.toNNReal x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ
      ≤ ∫⁻ _ in Ioc 0 (N : ℝ), c := lintegral_mono fun s => hb _
    _ < ⊤ := by
      rw [setLIntegral_const, Real.volume_Ioc]
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc) ENNReal.ofReal_lt_top

variable (μ) in
/-- The Picard space: `L²(dt ⊗ P)` classes on `(0,N]` with a raw predictable version. -/
abbrev PicardSpace (N : ℝ≥0) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  lpMeas E ℝ (rawPredictable S κ) 2 (timeProbMeasure N (driverLaw (κ := κ) μ))

instance picardSpace_complete (N : ℝ≥0) : CompleteSpace (PicardSpace (κ := κ) μ N E) := by
  have : Fact (rawPredictable S κ ≤ (inferInstance : MeasurableSpace (ℝ × DriverSample S κ))) :=
    ⟨predictableSpace_le _⟩
  infer_instance

/-- The chosen representative of a Picard class. -/
abbrev rep {N : ℝ≥0} (Z : PicardSpace (κ := κ) μ N E) : ℝ × DriverSample S κ → E :=
  ((Z : Lp E 2 (timeProbMeasure N (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → E)

omit [IsProbabilityMeasure μ] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
theorem aesm_rep {N : ℝ≥0} (Z : PicardSpace (κ := κ) μ N E) :
    AEStronglyMeasurable[rawPredictable S κ] (rep Z) (timeProbMeasure N (driverLaw (κ := κ) μ)) :=
  lpMeas.aestronglyMeasurable Z

omit [MeasurableSpace E] [BorelSpace E] in
/-- The time-constant initial value is a.e. raw predictable. -/
theorem aesm_initial {N : ℝ≥0} {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ) :
    AEStronglyMeasurable[rawPredictable S κ] (fun p : ℝ × DriverSample S κ => ξ p.2)
      (timeProbMeasure N (driverLaw (κ := κ) μ)) :=
  aesm_processFun (Y := fun _ => ξ) (fun _ => hξ.mono ((driverAugmented (κ := κ) μ).mono zero_le))
    (Eventually.of_forall fun _ => continuous_const)

/-- Drift of the Picard map, clamped at the horizon. -/
def picardDrift (c : LipCoeff κ E) {N : ℝ≥0} (ξ : DriverSample S κ → E)
    (Z : PicardSpace (κ := κ) μ N E) (t : ℝ≥0) (x : DriverSample S κ) : E :=
  ∫ s in Ioc (0 : ℝ) ((min t N : ℝ≥0) : ℝ), c.b (ξ x + rep Z (s, x))

/-- Noise integrands of the Picard map (coordinate `j`). -/
def picardNoiseFun (c : LipCoeff κ E) {N : ℝ≥0} (ξ : DriverSample S κ → E)
    (Z : PicardSpace (κ := κ) μ N E) (j : Fin (Module.finrank ℝ E)) :
    κ → ℝ × DriverSample S κ → ℝ :=
  fun a p => coordCLM E j (c.σ a (ξ p.2 + rep Z p))

omit [MeasurableSpace E] [BorelSpace E] in
theorem nativeIntegrand_picardNoiseFun (c : LipCoeff κ E) {N : ℝ≥0} {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ) (Z : PicardSpace (κ := κ) μ N E)
    (j : Fin (Module.finrank ℝ E)) : NativeIntegrand μ N (picardNoiseFun c ξ Z j) := by
  intro a
  have hc : Continuous fun y : E => coordCLM E j (c.σ a y) :=
    (coordCLM E j).continuous.comp (c.lip_σ a).continuous
  have hm : AEStronglyMeasurable[rawPredictable S κ] (picardNoiseFun c ξ Z j a)
      (timeProbMeasure N (driverLaw (κ := κ) μ)) :=
    hc.comp_aestronglyMeasurable ((aesm_initial (N := N) hξ).add (aesm_rep Z))
  refine ⟨hm, MemLp.of_bound (hm.mono (predictableSpace_le _)) (‖coordCLM E j‖ * c.C)
    (Eventually.of_forall fun p => ?_)⟩
  exact ((coordCLM E j).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (c.bd_σ a _) (norm_nonneg _))

/-- Noise processes of the Picard map (the continuous stochastic integrals). -/
def picardNoise (c : LipCoeff κ E) {N : ℝ≥0} {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ) (Z : PicardSpace (κ := κ) μ N E)
    (j : Fin (Module.finrank ℝ E)) : ℝ≥0 → DriverSample S κ → ℝ :=
  nativeAdaptedLimit μ N (nativeIntegrand_picardNoiseFun c hξ Z j).family

/-- The Picard process `D_Z + ∑_j M_Z^j e_j`. -/
def picardProc (c : LipCoeff κ E) {N : ℝ≥0} {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ) (Z : PicardSpace (κ := κ) μ N E)
    (t : ℝ≥0) (x : DriverSample S κ) : E :=
  picardDrift c ξ Z t x + ∑ j, picardNoise c hξ Z j t x • Module.finBasis ℝ E j

end BlockBand.SourceProcess.Stochastic.NativeSDE
