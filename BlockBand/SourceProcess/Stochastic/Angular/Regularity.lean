module

public import BlockBand.SourceProcess.Stochastic.Angular.Frame
public import BlockBand.SourceProcess.Stochastic.Dyson.Bounds

/-!
# Complex angular contract: regularity and bounds of `arrayFn` and `arrGen`

For a deterministic phase-invariant `C²` test `f₀` and a frame `V`:
* `contDiffAt_arrayFn`: `arrayFn V f₀` is `C²` at every point of simple spectrum;
* `continuousOn_arrGen`: `arrGen V f₀` is continuous on the simple-spectrum set;
* `measurable_arrayFn`, `measurable_arrGen`;
* `abs_arrayFn_le`: `arrayFn` is bounded; `abs_arrGen_le`: `arrGen` is bounded on gaps `≥ 1/n`.
The generic estimates `abs_pairTerm_le`, `abs_gen_le` (pair terms through `‖Df‖`, `‖D²f‖`,
couplings `≤ n²/N`) are reused for random tests.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory Filter Topology Matrix Set
open scoped Matrix ComplexConjugate ContDiff
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

variable {N r : ℕ}

/-!
### Pair terms
-/

/-- The pair term `(X_ij² + Y_ij²) f (Z)` of the generator. -/
def pairTerm (f : AngularArray N r → ℝ) (i j : Fin N) (Z : AngularArray N r) : ℝ :=
  fderiv ℝ (fderiv ℝ f) Z (pairRotX i j Z) (pairRotX i j Z) +
    fderiv ℝ f Z (pairRotX i j (pairRotX i j Z)) +
    fderiv ℝ (fderiv ℝ f) Z (pairRotY i j Z) (pairRotY i j Z) +
    fderiv ℝ f Z (pairRotY i j (pairRotY i j Z))

theorem gen_eq_sum (lam : Fin N → ℝ) (f : AngularArray N r → ℝ) (Z : AngularArray N r) :
    complexAngularGenerator N r lam f Z = (1 / 4 : ℝ) * ∑ i, ∑ j ∈ Finset.univ.filter
      (fun j => i < j), dysonCoupling N lam i j * pairTerm f i j Z := rfl

theorem norm_pairRotX_le (i j : Fin N) (Z : AngularArray N r) : ‖pairRotX i j Z‖ ≤ ‖Z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
  unfold pairRotX
  split_ifs
  · exact norm_le_pi_norm Z j
  · rw [norm_neg]; exact norm_le_pi_norm Z i
  · simp

theorem norm_pairRotY_le (i j : Fin N) (Z : AngularArray N r) : ‖pairRotY i j Z‖ ≤ ‖Z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
  unfold pairRotY
  split_ifs
  · rw [norm_smul, Complex.norm_I, one_mul]; exact norm_le_pi_norm Z j
  · rw [norm_smul, Complex.norm_I, one_mul]; exact norm_le_pi_norm Z i
  · simp

theorem continuous_pairRotX (i j : Fin N) : Continuous (pairRotX (r := r) i j) := by
  refine continuous_pi fun k => ?_
  unfold pairRotX
  split_ifs
  · exact continuous_apply j
  · exact (continuous_apply i).neg
  · exact continuous_const

theorem continuous_pairRotY (i j : Fin N) : Continuous (pairRotY (r := r) i j) := by
  refine continuous_pi fun k => ?_
  unfold pairRotY
  split_ifs
  · exact (continuous_apply j).const_smul Complex.I
  · exact (continuous_apply i).const_smul Complex.I
  · exact continuous_const

theorem continuous_pairTerm {f : AngularArray N r → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin N) :
    Continuous (pairTerm f i j) := by
  have h1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv two_ne_zero
  have h2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hX := continuous_pairRotX (r := r) i j
  have hY := continuous_pairRotY (r := r) i j
  unfold pairTerm
  refine (((h2.clm_apply hX).clm_apply hX).add (h1.clm_apply (hX.comp hX))).add
    (((h2.clm_apply hY).clm_apply hY).add (h1.clm_apply (hY.comp hY))) |>.congr fun Z => ?_
  simp only [Function.comp_apply, Pi.add_apply]; ring

/-- Pair terms through the derivative norms. -/
theorem abs_pairTerm_le (f : AngularArray N r → ℝ) (i j : Fin N) (Z : AngularArray N r)
    {C : ℝ} (h1 : ‖fderiv ℝ f Z‖ ≤ C) (h2 : ‖fderiv ℝ (fderiv ℝ f) Z‖ ≤ C) :
    |pairTerm f i j Z| ≤ 2 * C * (‖Z‖ ^ 2 + ‖Z‖) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans h1
  have b2 : ∀ W : AngularArray N r, ‖W‖ ≤ ‖Z‖ →
      |fderiv ℝ (fderiv ℝ f) Z W W| ≤ C * ‖Z‖ ^ 2 := fun W hW => by
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (fderiv ℝ f) Z W W‖ ≤ ‖fderiv ℝ (fderiv ℝ f) Z W‖ * ‖W‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) Z‖ * ‖W‖ * ‖W‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ C * ‖Z‖ * ‖Z‖ := by gcongr
      _ = C * ‖Z‖ ^ 2 := by ring
  have b1 : ∀ W : AngularArray N r, ‖W‖ ≤ ‖Z‖ → |fderiv ℝ f Z W| ≤ C * ‖Z‖ := fun W hW => by
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
  have hX := norm_pairRotX_le i j Z
  have hY := norm_pairRotY_le i j Z
  have hXX := (norm_pairRotX_le i j _).trans hX
  have hYY := (norm_pairRotY_le i j _).trans hY
  unfold pairTerm
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add_left (abs_add_le _ _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (abs_add_le _ _) _) _).trans ?_
  linarith [b2 _ hX, b1 _ hXX, b2 _ hY, b1 _ hYY]

/-- The generator through bounds on couplings and pair terms. -/
theorem abs_gen_le (lam : Fin N → ℝ) (f : AngularArray N r → ℝ) (Z : AngularArray N r)
    {c K : ℝ} (hc0 : 0 ≤ c) (hK0 : 0 ≤ K) (hc : ∀ i j, i ≠ j → dysonCoupling N lam i j ≤ c)
    (hK : ∀ i j, |pairTerm f i j Z| ≤ K) :
    |complexAngularGenerator N r lam f Z| ≤ N * N * c * K := by
  rw [gen_eq_sum, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  have hsum : |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      dysonCoupling N lam i j * pairTerm f i j Z| ≤ ∑ _i : Fin N, ∑ _j : Fin N, c * K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j hj => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => mul_nonneg hc0 hK0)
    have hij : i ≠ j := (Finset.mem_filter.1 hj).2.ne
    rw [abs_mul, abs_of_nonneg (coupling_nonneg lam i j)]
    exact mul_le_mul (hc i j hij) (hK i j) (abs_nonneg _) hc0
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  nlinarith [mul_nonneg hc0 hK0, mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) N)
    (Nat.cast_nonneg (α := ℝ) N)) (mul_nonneg hc0 hK0)]

/-!
### Bounds of angular arrays
-/

/-- A bound for angular arrays of unit vectors. -/
def frameBound (V : Matrix (Fin N) (Fin r) ℂ) : ℝ := ∑ a, ∑ b, ‖V b a‖

theorem frameBound_nonneg (V : Matrix (Fin N) (Fin r) ℂ) : 0 ≤ frameBound V := by
  unfold frameBound; positivity

theorem norm_angularArray_le' (V : Matrix (Fin N) (Fin r) ℂ) {u : Fin N → Fin N → ℂ}
    (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) : ‖angularArray V u‖ ≤ frameBound V := by
  refine (pi_norm_le_iff_of_nonneg (frameBound_nonneg V)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (frameBound_nonneg V)).2 fun a => ?_
  exact (norm_angularArray_le V hu i a).trans (Finset.single_le_sum
    (f := fun a => ∑ b, ‖V b a‖) (fun _ _ => by positivity) (Finset.mem_univ a))

theorem norm_arrZ_le (V : Matrix (Fin N) (Fin r) ℂ) {y : Fin (N * N) → ℝ}
    (hy : y ∈ simpleSet N) : ‖arrZ V y‖ ≤ frameBound V :=
  norm_angularArray_le' V (canon_unit hy)

/-- Uniform bound of `|f|`, `‖Df‖`, `‖D²f‖` on a ball for a `C²` test. -/
theorem exists_C2_bound {f : AngularArray N r → ℝ} (hf : ContDiff ℝ 2 f) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ Z : AngularArray N r, ‖Z‖ ≤ R →
      |f Z| ≤ C ∧ ‖fderiv ℝ f Z‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ f) Z‖ ≤ C := by
  have h1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv two_ne_zero
  have h2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hK := isCompact_closedBall (0 : AngularArray N r) R
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn h1.norm.continuousOn
  have h2n : Continuous fun Z => ‖fderiv ℝ (fderiv ℝ f) Z‖ :=
    (continuous_norm (E := AngularArray N r →L[ℝ] AngularArray N r →L[ℝ] ℝ)).comp h2
  obtain ⟨C2, hC2⟩ := hK.bddAbove_image h2n.continuousOn
  refine ⟨max (max C0 C1) (max C2 0), by positivity, fun Z hZ => ?_⟩
  have hm : Z ∈ Metric.closedBall (0 : AngularArray N r) R := mem_closedBall_zero_iff.2 hZ
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.norm_eq_abs]
    exact (hC0 Z hm).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have := hC1 Z hm; rw [norm_norm] at this
    exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
  · have : ‖fderiv ℝ (fderiv ℝ f) Z‖ ≤ C2 := hC2 ⟨Z, hm, rfl⟩
    exact this.trans ((le_max_left _ _).trans (le_max_right _ _))

/-!
### Regularity of `arrayFn` and `arrGen`
-/

variable {V : Matrix (Fin N) (Fin r) ℂ} {f₀ : AngularArray N r → ℝ}

theorem arrayFn_of_mem {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) :
    arrayFn V f₀ y = f₀ (arrZ V y) := by
  simp [arrayFn, hy]

theorem arrGen_of_mem {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) :
    arrGen V f₀ y = complexAngularGenerator N r (fun i => lam N i y) f₀ (arrZ V y) := by
  simp [arrGen, hy]

/-- **`arrayFn` is `C²` on the simple-spectrum set.** -/
theorem contDiffAt_arrayFn (hf : ContDiff ℝ 2 f₀) (hp : IsPhaseInvariant f₀)
    {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) : ContDiffAt ℝ 2 (arrayFn V f₀) y := by
  obtain ⟨κ, hκ⟩ := eventually_frame hy
  have hev : arrayFn V f₀ =ᶠ[𝓝 y] fun y' => f₀ (frameArr V κ y') := by
    filter_upwards [hκ] with y' hy'
    rw [arrayFn_of_mem hy'.1, phaseInv_frame hp V hy'.1 hy'.2]
  exact (hf.contDiffAt.comp y (contDiffAt_frameArr V hy hκ.self_of_nhds.2)).congr_of_eventuallyEq
    hev

theorem continuousAt_gen_frame (hf : ContDiff ℝ 2 f₀) {κ : Fin N → Fin N}
    {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (hκ : ∀ i, 0 < (proj N i y (κ i) (κ i)).re) :
    ContinuousAt (fun y' => complexAngularGenerator N r (fun i => lam N i y') f₀
      (frameArr V κ y')) y := by
  have hZ : ContinuousAt (frameArr V κ) y := (contDiffAt_frameArr (n := 0) V hy hκ).continuousAt
  simp only [gen_eq_sum]
  refine continuousAt_const.mul (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j hj => ?_)
  have hij : i ≠ j := (Finset.mem_filter.1 hj).2.ne
  have hN : (N : ℝ) ≠ 0 := by have := i.pos; positivity
  have hli := (contDiffAt_eigenvalue (n := 0) hy i).continuousAt
  have hlj := (contDiffAt_eigenvalue (n := 0) hy j).continuousAt
  refine ContinuousAt.mul ?_ ((continuous_pairTerm hf i j).continuousAt.comp hZ)
  unfold dysonCoupling
  refine continuousAt_const.div (continuousAt_const.mul ((hli.sub hlj).pow 2)) ?_
  exact mul_ne_zero hN (pow_ne_zero 2 (sub_ne_zero.mpr (HasSimpleSpectrum.ne hy hij)))

/-- **`arrGen` is continuous on the simple-spectrum set.** -/
theorem continuousOn_arrGen (hf : ContDiff ℝ 2 f₀) (hp : IsPhaseInvariant f₀) :
    ContinuousOn (arrGen V f₀) (simpleSet N) := by
  intro y hy
  obtain ⟨κ, hκ⟩ := eventually_frame hy
  have hev : arrGen V f₀ =ᶠ[𝓝 y] fun y' => complexAngularGenerator N r (fun i => lam N i y') f₀
      (frameArr V κ y') := by
    filter_upwards [hκ] with y' hy'
    rw [arrGen_of_mem hy'.1, gen_frame hp _ V hy'.1 hy'.2]
  exact ((continuousAt_gen_frame hf hy hκ.self_of_nhds.2).congr hev.symm).continuousWithinAt

theorem continuousOn_arrayFn (hf : ContDiff ℝ 2 f₀) (hp : IsPhaseInvariant f₀) :
    ContinuousOn (arrayFn V f₀) (simpleSet N) := fun _ hy =>
  (contDiffAt_arrayFn hf hp hy).continuousAt.continuousWithinAt

theorem measurable_of_continuousOn_simple {g : (Fin (N * N) → ℝ) → ℝ}
    (hg : ContinuousOn g (simpleSet N)) (h0 : ∀ y, y ∉ simpleSet N → g y = 0) : Measurable g := by
  classical
  have hm := ContinuousOn.measurable_piecewise hg (continuousOn_const (c := (0 : ℝ)))
    isOpen_simpleSet.measurableSet
  convert hm using 1
  funext y
  by_cases hy : y ∈ simpleSet N
  · simp [Set.piecewise, hy]
  · simp [Set.piecewise, hy, h0 y hy]

theorem measurable_arrayFn (hf : ContDiff ℝ 2 f₀) (hp : IsPhaseInvariant f₀) :
    Measurable (arrayFn V f₀) :=
  measurable_of_continuousOn_simple (continuousOn_arrayFn hf hp) fun y hy => by simp [arrayFn, hy]

theorem measurable_arrGen (hf : ContDiff ℝ 2 f₀) (hp : IsPhaseInvariant f₀) :
    Measurable (arrGen V f₀) :=
  measurable_of_continuousOn_simple (continuousOn_arrGen hf hp) fun y hy => by simp [arrGen, hy]

/-- **`arrayFn` is bounded.** -/
theorem abs_arrayFn_le (hf : ContDiff ℝ 2 f₀) : ∃ C, ∀ y, |arrayFn V f₀ y| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_C2_bound hf (frameBound V)
  refine ⟨C, fun y => ?_⟩
  by_cases hy : y ∈ simpleSet N
  · rw [arrayFn_of_mem hy]; exact (hC _ (norm_arrZ_le V hy)).1
  · simp [arrayFn, hy, hC0]

/-- Couplings at gaps `≥ 1/n` are at most `n²/N`. -/
theorem coupling_le_gap {lam : Fin N → ℝ} {n : ℕ} (hn : 0 < n)
    (hgap : ∀ i j : Fin N, i ≠ j → 1 / (n : ℝ) ≤ |lam i - lam j|) (i j : Fin N) (hij : i ≠ j) :
    dysonCoupling N lam i j ≤ 1 / (N * (1 / (n : ℝ)) ^ 2) :=
  coupling_le (by positivity) (hgap i j hij)

/-- **`arrGen` is bounded on gaps `≥ 1/n`.** -/
theorem abs_arrGen_le (hf : ContDiff ℝ 2 f₀) {n : ℕ} (hn : 0 < n) :
    ∃ C, ∀ y ∈ simpleSet N, (∀ i j : Fin N, i ≠ j → 1 / (n : ℝ) ≤ |lam N i y - lam N j y|) →
      |arrGen V f₀ y| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_C2_bound hf (frameBound V)
  set R := frameBound V
  refine ⟨N * N * (1 / (N * (1 / (n : ℝ)) ^ 2)) * (2 * C * (R ^ 2 + R)), fun y hy hgap => ?_⟩
  rw [arrGen_of_mem hy]
  have hZ := norm_arrZ_le V hy
  obtain ⟨-, h1, h2⟩ := hC _ hZ
  have hR := frameBound_nonneg V
  refine abs_gen_le _ _ _ (by positivity) (by positivity) (coupling_le_gap hn hgap) fun i j => ?_
  refine (abs_pairTerm_le f₀ i j _ h1 h2).trans ?_
  have : ‖arrZ V y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hZ 2
  gcongr

end BlockBand.SourceProcess.Stochastic.ComplexAngular
