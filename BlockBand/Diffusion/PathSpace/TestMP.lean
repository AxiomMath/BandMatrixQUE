module
public import BlockBand.SourceProcess.Stochastic.MartingaleProblem
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The test-function martingale problem and localized test functions

* `IsMPTest U f`: `f : ℝ^d → ℝ` is `C^∞`, compactly supported, with `tsupport f ⊆ U`.
* `IsTestMPSolution Q 𝓖 b a U Z`: the *raw* test-function martingale problem on an arbitrary
  filtered probability space (raw filtration: not completed, not right-continuous): `Z` is
  adapted (`Measurable[𝓖 t] (Z t)`), has a.s. continuous paths, and for every test `f` the raw
  process `f(Z_t) - ∫_0^t 𝓛f(Z_u) du` is a `𝓖`-martingale. This is the shape of
  `IsBaseDiffusion` (there with `U = univ`, state `ℝ × ℝ`).
* Localized tests: for a relatively compact subdomain `W` of an open `U` there is a test
  `χ` equal to `1` on an open neighbourhood `V` of `closure W` (`exists_bump`); then
  `χ · y_i` and `χ · y_i y_j` are tests, equal near `V` to `y_i` and `y_i y_j`, with generators
  `b_i` and `b_i y_j + b_j y_i + (a_ij + a_ji)/2` on `V` (`mpGenerator_coord`,
  `mpGenerator_coordMul`, `mpGenerator_congr`).
* For a test `f` and coefficients continuous on `U`, `𝓛f` is continuous with compact support
  (`continuous_mpGenerator`, `hasCompactSupport_mpGenerator`), hence bounded.
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open scoped NNReal

variable {d : ℕ}

/-- A smooth compactly supported test function supported in `U`. -/
def IsMPTest (U : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ U

/-- **The raw test-function martingale problem** for `𝓛 = mpGenerator b a` in `U`, on an
arbitrary filtered probability space with a raw filtration. -/
structure IsTestMPSolution {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (b : (Fin d → ℝ) → Fin d → ℝ) (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (U : Set (Fin d → ℝ)) (Z : ℝ≥0 → Ω → Fin d → ℝ) : Prop where
  adapted : ∀ t, Measurable[𝓖 t] (Z t)
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => Z t ω
  martingale : ∀ f, IsMPTest U f →
    Martingale (fun t ω => f (Z t ω) - ∫ u in Ioc (0 : ℝ) t, mpGenerator b a f (Z u.toNNReal ω))
      𝓖 Q

/-!
### Bumps and localized tests
-/

/-- A test equal to `1` on an open neighbourhood of `closure W`. -/
theorem exists_bump {U W : Set (Fin d → ℝ)} (hU : IsOpen U) (hW : IsInteriorDomain W U) :
    ∃ χ : (Fin d → ℝ) → ℝ, ∃ V : Set (Fin d → ℝ), IsMPTest U χ ∧ IsOpen V ∧
      closure W ⊆ V ∧ ∀ y ∈ V, χ y = 1 := by
  obtain ⟨V₂, hV₂o, hKV₂, hV₂U, hV₂c⟩ :=
    exists_open_between_and_isCompact_closure hW.2.1 hU hW.2.2
  obtain ⟨V₁, hV₁o, hKV₁, hV₁V₂, -⟩ :=
    exists_open_between_and_isCompact_closure hW.2.1 hV₂o hKV₂
  obtain ⟨χ, hχ, -, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    hV₂o isClosed_closure hV₁V₂
  have hts : tsupport χ = closure V₂ := by rw [tsupport, hsupp]
  refine ⟨χ, V₁, ⟨hχ, ?_, hts ▸ hV₂U⟩, hV₁o, hKV₁, fun y hy => (hone y).1 (subset_closure hy)⟩
  rw [HasCompactSupport, hts]; exact hV₂c

theorem IsMPTest.mul_left {U : Set (Fin d → ℝ)} {χ p : (Fin d → ℝ) → ℝ} (hχ : IsMPTest U χ)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) : IsMPTest U (fun y => χ y * p y) :=
  ⟨hχ.1.mul hp, hχ.2.1.mul_right, (tsupport_mul_subset_left).trans hχ.2.2⟩

/-- The generator only depends on the germ of the test function. -/
theorem mpGenerator_congr {b : (Fin d → ℝ) → Fin d → ℝ}
    {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {f g : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ}
    (h : f =ᶠ[𝓝 y] g) : mpGenerator b a f y = mpGenerator b a g y := by
  simp only [mpGenerator, h.fderiv_eq, h.fderiv.fderiv_eq]

theorem eventuallyEq_mul_of_eq_one {χ p : (Fin d → ℝ) → ℝ} {V : Set (Fin d → ℝ)}
    (hV : IsOpen V) (hχ : ∀ y ∈ V, χ y = 1) {y : Fin d → ℝ} (hy : y ∈ V) :
    (fun y => χ y * p y) =ᶠ[𝓝 y] p := by
  filter_upwards [hV.mem_nhds hy] with z hz
  rw [hχ z hz, one_mul]

/-- The generator of a coordinate is the drift coordinate. -/
theorem mpGenerator_coord (b : (Fin d → ℝ) → Fin d → ℝ)
    (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (i : Fin d) (y : Fin d → ℝ) :
    mpGenerator b a (fun y => y i) y = b y i := by
  have h1 : fderiv ℝ (fun y : Fin d → ℝ => y i) =
      fun _ => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i := by
    funext z; exact (hasFDerivAt_apply i z).fderiv
  simp only [mpGenerator, h1, ContinuousLinearMap.proj_apply]
  simp [Pi.single_apply]

/-- The generator of `y_i y_j`. -/
theorem mpGenerator_coordMul (b : (Fin d → ℝ) → Fin d → ℝ)
    (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) (y : Fin d → ℝ) :
    mpGenerator b a (fun y => y i * y j) y =
      b y i * y j + b y j * y i + (a y i j + a y j i) / 2 := by
  set Pi_ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i
  set Pj := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j
  have hD : ∀ z : Fin d → ℝ, HasFDerivAt (fun y : Fin d → ℝ => y i * y j)
      (z i • Pj + z j • Pi_) z := fun z =>
    (hasFDerivAt_apply i z).mul (hasFDerivAt_apply j z)
  have h1 : fderiv ℝ (fun y : Fin d → ℝ => y i * y j) = fun z => z i • Pj + z j • Pi_ :=
    funext fun z => (hD z).fderiv
  have hD2 : HasFDerivAt (fun z : Fin d → ℝ => z i • Pj + z j • Pi_)
      (Pi_.smulRight Pj + Pj.smulRight Pi_) y :=
    ((hasFDerivAt_apply i y).smul_const Pj).add ((hasFDerivAt_apply j y).smul_const Pi_)
  have key : ∀ v w : Fin d → ℝ,
      (Pi_.smulRight Pj + Pj.smulRight Pi_) v w = v i * w j + v j * w i := fun v w => by
    simp [Pi_, Pj]
  have key1 : ∀ v : Fin d → ℝ, (y i • Pj + y j • Pi_) v = y i * v j + y j * v i := fun v => by
    simp [Pi_, Pj]
  rw [mpGenerator, h1, hD2.fderiv]
  simp only [key, key1]
  simp [Pi.single_apply, mul_add, Finset.sum_add_distrib]
  ring

/-!
### Regularity of `𝓛f` for a test `f`
-/

/-- A function continuous on an open `U`, times a continuous function supported in `U`, is
continuous. -/
theorem continuous_mul_of_tsupport {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {g h : (Fin d → ℝ) → ℝ} (hg : ContinuousOn g U) (hh : Continuous h) (hsupp : tsupport h ⊆ U) :
    Continuous fun y => g y * h y := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : y ∈ U
  · exact (hg.continuousAt (hU.mem_nhds hy)).mul hh.continuousAt
  · have h0 : h =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h' => hy (hsupp h')
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [h0] with z hz
    simp [hz]

theorem tsupport_fderiv_apply_subset {f : (Fin d → ℝ) → ℝ} (v : Fin d → ℝ) :
    tsupport (fun y => fderiv ℝ f y v) ⊆ tsupport f :=
  closure_minimal (fun y hy => support_fderiv_subset ℝ (fun h => hy (by simp [h])))
    (isClosed_tsupport f)

theorem tsupport_fderiv_fderiv_apply_subset {f : (Fin d → ℝ) → ℝ} (v w : Fin d → ℝ) :
    tsupport (fun y => fderiv ℝ (fderiv ℝ f) y v w) ⊆ tsupport f :=
  closure_minimal (fun y hy => tsupport_fderiv_subset ℝ (f := f)
      (support_fderiv_subset ℝ (f := fderiv ℝ f) (fun h => hy (by simp [h]))))
    (isClosed_tsupport f)

/-- `𝓛f` is continuous for a test `f` and coefficients continuous on `U`. -/
theorem continuous_mpGenerator {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    (hb : ContinuousOn b U) (ha : ContinuousOn a U) {f : (Fin d → ℝ) → ℝ} (hf : IsMPTest U f) :
    Continuous (mpGenerator b a f) := by
  have hf1 : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv (by simp)
  have hf2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous_fderiv (by simp)
  unfold mpGenerator
  refine (continuous_finsetSum _ fun k _ => ?_).add
    (continuous_const.mul (continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_))
  · exact continuous_mul_of_tsupport hU (((continuous_apply k).comp_continuousOn hb))
      (hf1.clm_apply continuous_const) ((tsupport_fderiv_apply_subset _).trans hf.2.2)
  · exact continuous_mul_of_tsupport hU
      ((continuous_id.matrix_elem k l).comp_continuousOn ha)
      ((hf2.clm_apply continuous_const).clm_apply continuous_const)
      ((tsupport_fderiv_fderiv_apply_subset _ _).trans hf.2.2)

theorem mpGenerator_eq_zero_of_notMem {b : (Fin d → ℝ) → Fin d → ℝ}
    {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {f : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ}
    (hy : y ∉ tsupport f) : mpGenerator b a f y = 0 := by
  have h1 : fderiv ℝ f y = 0 := fderiv_of_notMem_tsupport ℝ hy
  have h2 : fderiv ℝ (fderiv ℝ f) y = 0 :=
    fderiv_of_notMem_tsupport ℝ fun h => hy (tsupport_fderiv_subset ℝ h)
  simp [mpGenerator, h1, h2]

theorem hasCompactSupport_mpGenerator {U : Set (Fin d → ℝ)} {b : (Fin d → ℝ) → Fin d → ℝ}
    {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {f : (Fin d → ℝ) → ℝ} (hf : IsMPTest U f) :
    HasCompactSupport (mpGenerator b a f) :=
  hf.2.1.mono' fun y hy => by
    by_contra h; exact hy (mpGenerator_eq_zero_of_notMem h)

/-- `𝓛f` is bounded for a test `f`. -/
theorem exists_bound_mpGenerator {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    (hb : ContinuousOn b U) (ha : ContinuousOn a U) {f : (Fin d → ℝ) → ℝ} (hf : IsMPTest U f) :
    ∃ C, 0 ≤ C ∧ ∀ y, |mpGenerator b a f y| ≤ C := by
  obtain ⟨C, hC⟩ := (continuous_mpGenerator hU hb ha hf).bounded_above_of_compact_support
    (hasCompactSupport_mpGenerator hf)
  exact ⟨max C 0, le_max_right _ _, fun y => (Real.norm_eq_abs _ ▸ hC y).trans (le_max_left _ _)⟩

end BlockBand.Diffusion
