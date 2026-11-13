module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.VersionAlpha
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# PSD-valued predictable versions of matrix densities

Setting: an arbitrary measurable space `(Ω, m₀)`, raw filtration `𝓖`, a finite index type `ι`,
a `𝓖`-adapted process `Y : ℝ≥0 → Ω → E` (no joint measurability, no path regularity required
for the measurability statements), a raw `𝓖`-stopping time `τ`, and a matrix of continuous
coefficients `φ i j : E → ℝ` that is positive semidefinite **everywhere** on `E`
(`0 ≤ ∑_{ij} v_i v_j φ_{ij}(y)` for all `y`, `v`). The intended density matrix is
`a^{ij}_s(ω) = φ_{ij}(Y_s ω) 1{s ≤ τ ω}`.

The entrywise `alphaVersion` is a `limUnder` of left samples; where these diverge it is junk and
the matrix need not be PSD. The fix is to restrict to the set where all entries converge:

* `psdConvSet τ φ Y`: the set of `(s, ω)` where the left samples of **all** entries converge;
  raw predictable (`measurableSet_psdConvSet`, convergence set of predictable sequences).
* `psdVersion τ φ Y i j t ω = 1_G(t, ω) · alphaVersion τ (φ i j) Y t ω`.
  - `stronglyMeasurable_psdVersion`, `measurable_psdVersion`: raw predictable, jointly
    measurable through `s ↦ s.toNNReal` (the `IsL2IntegratorVec.measurable` form);
  - `psdVersion_psd`: PSD at **every** `(t, ω)` (limit of PSD left-sample matrices, which are
    `1{u < τ} φ(Y_u)`); `psdVersion_diag_nonneg`;
  - `psdVersion_eq`: on every continuous path and every `t > 0`,
    `psdVersion i j t ω = φ_{ij}(Y_t ω) 1{t ≤ τ ω}` (pathwise, no null set);
    `ae_psdVersion_eq` (a.s. for all `t > 0`), `setIntegral_psdVersion`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.Stochastic.Integral (leftPoint)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {E : Type*} [TopologicalSpace E]
  {ι : Type*} [Fintype ι]

omit mΩ [TopologicalSpace E] [Fintype ι] in
/-- The set where the left samples of every entry converge. -/
def psdConvSet (τ : Ω → WithTop ℝ≥0) (φ : ι → ι → E → ℝ) (Y : ℝ≥0 → Ω → E) : Set (ℝ × Ω) :=
  {p | ∀ i j, ∃ c, Tendsto (fun n => leftSample n (preComposite τ (φ i j) Y) p) atTop (𝓝 c)}

omit mΩ [TopologicalSpace E] [Fintype ι] in
/-- The PSD-valued version `1_G · alphaVersion` of the matrix density `φ(Y_s) 1{s ≤ τ}`. -/
def psdVersion (τ : Ω → WithTop ℝ≥0) (φ : ι → ι → E → ℝ) (Y : ℝ≥0 → Ω → E) (i j : ι)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  (psdConvSet τ φ Y).indicator (compositeVersion τ (φ i j) Y) ((t : ℝ), ω)

omit mΩ [TopologicalSpace E] [Fintype ι] in
theorem psdVersion_toNNReal (τ : Ω → WithTop ℝ≥0) (φ : ι → ι → E → ℝ) (Y : ℝ≥0 → Ω → E)
    (i j : ι) :
    (fun p : ℝ × Ω => psdVersion τ φ Y i j p.1.toNNReal p.2) =
      (psdConvSet τ φ Y).indicator (compositeVersion τ (φ i j) Y) := by
  funext p
  by_cases hp : 0 < p.1
  · simp only [psdVersion, Real.coe_toNNReal _ hp.le]
  · have hp' : p.1 ≤ 0 := not_lt.1 hp
    rw [psdVersion, Real.toNNReal_of_nonpos hp', NNReal.coe_zero,
      indicator_apply_eq_zero.2 fun _ => compositeVersion_of_nonpos τ (φ i j) Y (p := (0, p.2))
        le_rfl,
      indicator_apply_eq_zero.2 fun _ => compositeVersion_of_nonpos τ (φ i j) Y hp']

variable (𝓖 : Filtration ℝ≥0 mΩ) {τ : Ω → WithTop ℝ≥0} {φ : ι → ι → E → ℝ}
  {Y : ℝ≥0 → Ω → E}

omit [Fintype ι] in
/-- The convergence set is raw predictable. -/
theorem measurableSet_psdConvSet [Finite ι] (hτ : IsStoppingTime 𝓖 τ)
    (hφ : ∀ i j, Continuous (φ i j)) (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) :
    MeasurableSet[predictableSpace (toCF 𝓖)] (psdConvSet τ φ Y) := by
  have he : psdConvSet τ φ Y = ⋂ i, ⋂ j,
      {p | ∃ c, Tendsto (fun n => leftSample n (preComposite τ (φ i j) Y) p) atTop (𝓝 c)} := by
    ext p; simp [psdConvSet]
  rw [he]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  exact @StronglyMeasurable.measurableSet_exists_tendsto ℕ (ℝ × Ω) ℝ
    (predictableSpace (toCF 𝓖)) _ _ atTop _ _ _ fun n =>
      stronglyMeasurable_leftSample 𝓖 n (stronglyMeasurable_preComposite 𝓖 hτ (hφ i j) hY)

omit [Fintype ι] in
/-- **Raw predictable version** (read through `s ↦ s.toNNReal`). -/
theorem stronglyMeasurable_psdVersion [Finite ι] (hτ : IsStoppingTime 𝓖 τ)
    (hφ : ∀ i j, Continuous (φ i j)) (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) (i j : ι) :
    StronglyMeasurable[predictableSpace (toCF 𝓖)]
      fun p : ℝ × Ω => psdVersion τ φ Y i j p.1.toNNReal p.2 := by
  rw [psdVersion_toNNReal]
  exact (stronglyMeasurable_compositeVersion 𝓖 hτ (hφ i j) hY).indicator
    (measurableSet_psdConvSet 𝓖 hτ hφ hY)

omit [Fintype ι] in
/-- **Jointly measurable version**, in the form of `IsL2IntegratorVec.measurable`. -/
theorem measurable_psdVersion [Finite ι] (hτ : IsStoppingTime 𝓖 τ)
    (hφ : ∀ i j, Continuous (φ i j)) (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) (i j : ι) :
    Measurable fun p : ℝ × Ω => psdVersion τ φ Y i j p.1.toNNReal p.2 :=
  ((stronglyMeasurable_psdVersion 𝓖 hτ hφ hY i j).mono (predictableSpace_le _)).measurable

omit mΩ [TopologicalSpace E] in
/-- Left-sample matrices are PSD: they are `1{u < τ} φ(Y_u)` (or `0`). -/
theorem leftSample_psd (hpsd : ∀ y (v : ι → ℝ), 0 ≤ ∑ i, ∑ j, v i * v j * φ i j y)
    (n : ℕ) (p : ℝ × Ω) (v : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * v j * leftSample n (preComposite τ (φ i j) Y) p := by
  by_cases hp : 0 < p.1
  · by_cases hm : p.2 ∈ {ω | ((leftPoint n p.1 : ℝ≥0) : WithTop ℝ≥0) < τ ω}
    · simp only [leftSample, hp, ite_true, preComposite, indicator_of_mem hm]
      exact hpsd _ v
    · simp only [leftSample, hp, ite_true, preComposite, indicator_of_notMem hm, mul_zero,
        Finset.sum_const_zero, le_refl]
  · simp [leftSample, hp]

omit mΩ [TopologicalSpace E] in
/-- **The version is PSD everywhere.** -/
theorem psdVersion_psd (hpsd : ∀ y (v : ι → ℝ), 0 ≤ ∑ i, ∑ j, v i * v j * φ i j y)
    (t : ℝ≥0) (ω : Ω) (v : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * v j * psdVersion τ φ Y i j t ω := by
  by_cases hG : ((t : ℝ), ω) ∈ psdConvSet τ φ Y
  · simp only [psdVersion, indicator_of_mem hG]
    have hlim : Tendsto (fun n => ∑ i, ∑ j, v i * v j *
        leftSample n (preComposite τ (φ i j) Y) ((t : ℝ), ω)) atTop
        (𝓝 (∑ i, ∑ j, v i * v j * compositeVersion τ (φ i j) Y ((t : ℝ), ω))) :=
      tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        (tendsto_nhds_limUnder (hG i j)).const_mul _
    exact ge_of_tendsto' hlim fun n => leftSample_psd hpsd n _ v
  · simp [psdVersion, indicator_of_notMem hG]

omit mΩ [TopologicalSpace E] in
theorem psdVersion_diag_nonneg [DecidableEq ι]
    (hpsd : ∀ y (v : ι → ℝ), 0 ≤ ∑ i, ∑ j, v i * v j * φ i j y) (i : ι) (t : ℝ≥0) (ω : Ω) :
    0 ≤ psdVersion τ φ Y i i t ω := by
  have h := psdVersion_psd (Y := Y) (τ := τ) hpsd t ω (Pi.single i 1)
  simpa [Pi.single_apply, ite_mul, Finset.sum_ite_eq'] using h

omit mΩ [Fintype ι] in
/-- **Pathwise identification**: on every continuous path and every `t > 0`,
`psdVersion i j t ω = φ_{ij}(Y_t ω) 1{t ≤ τ ω}`. -/
theorem psdVersion_eq (hφ : ∀ i j, Continuous (φ i j)) {ω : Ω}
    (hω : Continuous fun t => Y t ω) {t : ℝ≥0} (ht : 0 < t) (i j : ι) :
    psdVersion τ φ Y i j t ω = if (t : WithTop ℝ≥0) ≤ τ ω then φ i j (Y t ω) else 0 := by
  have hG : ((t : ℝ), ω) ∈ psdConvSet τ φ Y := fun i' j' =>
    ⟨_, tendsto_leftSample_stoppedComposite τ (hφ i' j') (p := ((t : ℝ), ω)) hω
      (by exact_mod_cast ht)⟩
  rw [psdVersion, indicator_of_mem hG]
  exact alphaVersion_eq (hφ i j) hω ht

omit [Fintype ι] in
theorem ae_psdVersion_eq {Q : Measure Ω} (hφ : ∀ i j, Continuous (φ i j))
    (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω) (i j : ι) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t →
      psdVersion τ φ Y i j t ω = if (t : WithTop ℝ≥0) ≤ τ ω then φ i j (Y t ω) else 0 := by
  filter_upwards [hYc] with ω hω t ht using psdVersion_eq hφ hω ht i j

omit mΩ [Fintype ι] in
/-- Pathwise integrals of the version are those of the stopped composite. -/
theorem setIntegral_psdVersion (hφ : ∀ i j, Continuous (φ i j)) {ω : Ω}
    (hω : Continuous fun t => Y t ω) (i j : ι) (a b : ℝ) (ha : 0 ≤ a) :
    ∫ r in Ioc a b, psdVersion τ φ Y i j r.toNNReal ω =
      ∫ r in Ioc a b, stoppedComposite τ (φ i j) Y (r, ω) := by
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hr0 : 0 < r := ha.trans_lt hr.1
  rw [psdVersion_eq hφ hω (Real.toNNReal_pos.2 hr0), stoppedComposite]

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
