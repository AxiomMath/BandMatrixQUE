module

public import BlockBand.External.CEH.SourceStatement
public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Native.CEH.BlockBand.External.CEH.LocalLawMDEAdapter
public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEMatrixAdapter
public import BlockBand.Native.CEH.BlockBand.External.CEH.TypicalSpacingExistence
public import BlockBand.Native.CEH.BlockBand.External.CEH.TypicalSpacingLocalETHAssembly

/-!
# The deterministic fields of `SourceContract` and MDE identification

The deterministic fields `mde_exists`, `mde_unique_off_real` and `spacing_exists` of
`External.CEH.SourceContract`, proved from the explicit Hermitian MDE branch and the CEH typical
spacing, and `MDEBranchIdentification`, with no hypothesis.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH

open BlockBand.External.CEH
open CEHNative.BlockBand

/-- The source MDE solution predicate is the one with `s = λ²`. -/
theorem isMDESolution_iff_localETH {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N} {z : ℂ}
    {M : SourceMatrix N} :
    IsMDESolution lambda H0 z M ↔ IsLocalETHMDESolution (lambda ^ 2) H0.1 z M := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have : ((lambda ^ 2 : ℝ) : ℂ) = (lambda : ℂ) ^ 2 := by push_cast; ring
    rw [this]
    exact h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have : ((lambda ^ 2 : ℝ) : ℂ) = (lambda : ℂ) ^ 2 := by push_cast; ring
    rw [this] at h1
    exact h1

/-- The branch matrix: the explicit Hermitian branch off the real axis, `0` on it. -/
def branchMatrix {N : ℕ} {lambda : ℝ} (hl : 0 < lambda) (H0 : SourceHermitian N) (z : ℂ) :
    SourceMatrix N :=
  if z.im = 0 then 0 else CEH.hermitianMDEBranch H0.2 (pow_pos hl 2) z

theorem branchMatrix_of_im_ne {N : ℕ} {lambda : ℝ} (hl : 0 < lambda) (H0 : SourceHermitian N)
    {z : ℂ} (hz : z.im ≠ 0) :
    branchMatrix hl H0 z = CEH.hermitianMDEBranch H0.2 (pow_pos hl 2) z := by
  simp [branchMatrix, hz]

theorem continuousOn_hermitianMDEBranch {N : ℕ} {lambda : ℝ} (hl : 0 < lambda)
    (H0 : SourceHermitian N) :
    ContinuousOn (fun z => CEH.hermitianMDEBranch H0.2 (pow_pos hl 2) z) {z : ℂ | z.im ≠ 0} := by
  intro z hz
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : (fun z => CEH.hermitianMDEBranch H0.2 (pow_pos hl 2) z) = fun _ => 0 :=
      funext fun _ => Subsingleton.elim _ _
    rw [this]
    exact continuousWithinAt_const
  · refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
      CEH.continuousAt_hermitianMDEBranch_apply H0.2 hN (pow_pos hl 2) hz i j

/-- The MDE branch given by `branchMatrix`. -/
def nativeMDEBranch {N : ℕ} {lambda : ℝ} (hl : 0 < lambda) (H0 : SourceHermitian N) :
    MDEBranch lambda H0 where
  matrix := branchMatrix hl H0
  solution z hz := by
    rw [branchMatrix_of_im_ne hl H0 hz, isMDESolution_iff_localETH]
    exact CEH.hermitianMDEBranch_isSolution H0.2 (pow_pos hl 2) hz
  continuous_off_real := (continuousOn_hermitianMDEBranch hl H0).congr fun z hz =>
    branchMatrix_of_im_ne hl H0 hz
  measurable_entry a b := by
    have hs : MeasurableSet {z : ℂ | z.im = 0} :=
      measurableSet_eq_fun Complex.measurable_im measurable_const
    have h := ContinuousOn.measurable_piecewise (s := {z : ℂ | z.im = 0})
      (f := fun _ => (0 : ℂ))
      (g := fun z => CEH.hermitianMDEBranch H0.2 (pow_pos hl 2) z a b) continuousOn_const
      ((continuous_id.matrix_elem a b).comp_continuousOn
        ((continuousOn_hermitianMDEBranch hl H0).mono fun _ hz => hz))
      hs
    convert h using 1
    funext z
    by_cases hz : z.im = 0 <;> simp [branchMatrix, Set.piecewise, hz]

/-- **MDE existence**: for `N > 0`, `λ > 0` and Hermitian `H0` an MDE branch exists (the
`mde_exists` field of `External.CEH.SourceContract`). -/
theorem mde_exists : ∀ (N : ℕ), 0 < N → ∀ lambda : ℝ, 0 < lambda →
    ∀ H0 : SourceHermitian N, Nonempty (MDEBranch lambda H0) :=
  fun _ _ _ hl H0 => ⟨nativeMDEBranch hl H0⟩

/-- Every branch agrees with the explicit branch off ℝ. -/
theorem matrix_eq_hermitianBranch {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N}
    (hl : 0 < lambda) (M : MDEBranch lambda H0) {z : ℂ} (hz : z.im ≠ 0) :
    M.matrix z = CEH.hermitianMDEBranch H0.2 (pow_pos hl 2) z := by
  have h1 := isCEHMDESolution_iff_isLocalETHMDESolution.2
    (isMDESolution_iff_localETH.1 (M.solution z hz))
  have h2 := isCEHMDESolution_iff_isLocalETHMDESolution.2
    (CEH.hermitianMDEBranch_isSolution H0.2 (pow_pos hl 2) hz)
  exact cehMDE_unique N (lambda ^ 2) (pow_pos hl 2) H0 z _ _ h1 h2

/-- **MDE uniqueness off the real axis**: two MDE branches agree at every `z` with `Im z ≠ 0`
(the `mde_unique_off_real` field of `External.CEH.SourceContract`). -/
theorem mde_unique_off_real : ∀ {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N},
    0 < N → 0 < lambda → ∀ M M' : MDEBranch lambda H0,
      ∀ z : ℂ, z.im ≠ 0 → M.matrix z = M'.matrix z :=
  fun _ hl M M' _ hz => (matrix_eq_hermitianBranch hl M hz).trans (matrix_eq_hermitianBranch hl M' hz).symm

/-- The CEH typical spacing, as a typical spacing of every MDE branch (`N ≥ 4`, `λ > 0`). -/
def nativeTypicalSpacing {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N} (hN : 4 ≤ N)
    (hl : 0 < lambda) (M : MDEBranch lambda H0) : TypicalSpacing M where
  eta := CEH.cehTypicalSpacing N hN (CEH.hermitianSpectrum H0.2) (pow_pos hl 2)
  positive E := (CEH.cehTypicalSpacing_isLocalETHTypicalSpacing hN H0.2 (pow_pos hl 2) E).1
  measurable_eta := CEH.measurable_cehTypicalSpacing N hN _ (pow_pos hl 2)
  equation E := by
    have h := CEH.cehTypicalSpacing_isLocalETHTypicalSpacing hN H0.2 (pow_pos hl 2) E
    have hz : ((E : ℂ) + ((CEH.cehTypicalSpacing N hN (CEH.hermitianSpectrum H0.2)
        (pow_pos hl 2) E : ℝ) : ℂ) * Complex.I).im ≠ 0 := by
      simp [h.1.ne']
    rw [matrix_eq_hermitianBranch hl M hz]
    exact h.2

/-- **Typical-spacing existence**: every MDE branch with `N ≥ 4`, `λ > 0` has a typical spacing
(the `spacing_exists` field of `External.CEH.SourceContract`). -/
theorem spacing_exists : ∀ {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N},
    4 ≤ N → 0 < lambda → ∀ M : MDEBranch lambda H0, Nonempty (TypicalSpacing M) :=
  fun hN hl M => ⟨nativeTypicalSpacing hN hl M⟩

/-- The paper MDE is the one. -/
theorem isManuscriptMDE_iff_ceh {N : ℕ} {s : ℝ} {F : SourceHermitian N} {z : ℂ}
    {M : SourceMatrix N} :
    BlockBand.Internal.Contracts.Inputs.IsManuscriptMDE s F z M ↔ IsCEHMDESolution s F.1 z M :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **`MDEBranchIdentification`**, with no hypothesis. -/
theorem mdeBranchIdentification_holds :
    BlockBand.Internal.Contracts.Inputs.MDEBranchIdentification := by
  intro N _ s hs F
  have hl : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsq : ((Real.sqrt s : ℝ) : ℂ) ^ 2 = (s : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le]
  refine ⟨⟨nativeMDEBranch hl F⟩, fun M z hz => ?_, fun z _ M₁ M₂ h₁ h₂ => ?_⟩
  · obtain ⟨h1, h2⟩ := M.solution z hz
    rw [hsq] at h1
    exact ⟨h1, h2⟩
  · exact cehMDE_unique N s hs F z M₁ M₂ (isManuscriptMDE_iff_ceh.1 h₁)
      (isManuscriptMDE_iff_ceh.1 h₂)

end BlockBand.Native.CEH
