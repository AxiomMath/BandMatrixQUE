module

public import Mathlib
public import BlockBand.Wegner.ProjectedWegnerGUECount
public import BlockBand.Wegner.ProjectedWegnerDensity
public import BlockBand.Wegner.PoissonRepresentationMatrix

/-!
# One fresh GUE block against a dissipative background

Law: `z ∼ Johansson.coordinateMeasure W (c/W)`, so `A = (Johansson.gaussianMatrix z).1` has law
`gueMatrixLaw W (c/W)` (`GUE_W(c/W)`). Hypothesis: the mean count bound
`E N_{[a,b]}(F + A) ≤ C/√c · W · (b-a)` for all Hermitian `F` (`GUECountBound C`, supplied by
`gueCoordinate_count_le`).

* `lintegral_real_background_le`: for Hermitian `F`, `η > 0`,
  `E[-Im Tr (A + F + iη)⁻¹] ≤ π C/√c · W`;
* `lintegral_oneBlock_le`: for every deterministic `S` with imaginary margin `η > 0`
  (`Im ⟨v, S v⟩ ≥ η ‖v‖²`), `E[-Im Tr (A + S)⁻¹] ≤ π C/√c · W`. Write `S = F + iY + iη` with
  `F` Hermitian, `Y ⪰ 0`; the Poisson representation at `ζ = i` of
  `ζ ↦ Tr (A + F + ζY + iη)⁻¹`, Tonelli, and the real-background bound at `F + tY`.

Uniform in `S`, `η`, `W`, `c`; the constant is the one of `GUECountBound`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open MeasureTheory Set Complex Matrix
open BlockBand.External
open scoped ENNReal ComplexOrder

/-- The PSSS one-block mean count bound with constant `C` (conclusion of
`gueCoordinate_count_le`). -/
def GUECountBound (C : ℝ) : Prop :=
  ∀ (W : ℕ), 0 < W → ∀ (c : ℝ), 0 < c →
    ∀ (F : Matrix (Fin W) (Fin W) ℂ) (hF : F.IsHermitian) (a b : ℝ), a ≤ b →
      ∫⁻ z, (PSSS.eigenCount
          ⟨F + (Johansson.gaussianMatrix z).1,
            hF.add (Johansson.gaussianMatrix z).2⟩ (Set.Icc a b) : ENNReal)
          ∂(Johansson.coordinateMeasure W (Real.toNNReal (c / W))) ≤
        ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * (b - a))

/-- The count as a sum of indicators over increasing eigenvalues. -/
theorem eigenCount_eq_sum_indicator {ι : Type} [Fintype ι] [DecidableEq ι]
    (X : PSSS.HermitianMatrix ι) (J : Set ℝ) :
    (PSSS.eigenCount X J : ℝ≥0∞) = ∑ i, J.indicator (fun _ => (1 : ℝ≥0∞))
      (BlockBand.Foundations.Spectral.increasingEigenvalue X.2 i) := by
  classical
  unfold PSSS.eigenCount
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : BlockBand.Foundations.Spectral.increasingEigenvalue X.2 i ∈ J
  · simp [h]
  · simp [h]

theorem measurable_gaussianMatrix_val (W : ℕ) :
    Measurable (fun z : Johansson.UpperPair W → ℝ × ℝ => (Johansson.gaussianMatrix z).1) :=
  measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix

/-- **Real Hermitian background.** Under `GUECountBound C` (`C ≥ 0`), for `W > 0`, `c > 0`,
Hermitian `F` and `η > 0`: `E[-Im Tr (A + F + iη)⁻¹] ≤ π C/√c · W`, `A ∼ GUE_W(c/W)`. -/
theorem lintegral_real_background_le {C : ℝ} (hC : GUECountBound C) (hC0 : 0 ≤ C) {W : ℕ}
    (hW : 0 < W) {c : ℝ} (hc : 0 < c) {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian)
    {η : ℝ} (hη : 0 < η) :
    ∫⁻ z, ENNReal.ofReal
        (-((((Johansson.gaussianMatrix z).1 + F) + ((η : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹.trace).im)
        ∂(Johansson.coordinateMeasure W (Real.toNNReal (c / W))) ≤
      ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * Real.pi) := by
  set X : (Johansson.UpperPair W → ℝ × ℝ) → PSSS.HermitianMatrix (Fin W) :=
    fun z => ⟨F + (Johansson.gaussianMatrix z).1, hF.add (Johansson.gaussianMatrix z).2⟩
  have hval : Measurable (fun z : Johansson.UpperPair W → ℝ × ℝ =>
      F + (Johansson.gaussianMatrix z).1) := by
    rw [Matrix.measurable_iff]
    intro i j
    exact measurable_const.add ((Matrix.measurable_iff.mp (measurable_gaussianMatrix_val W)) i j)
  have hX : Measurable X := hval.subtype_mk
  have := Johansson.coordinateMeasure_probability W (Real.toNNReal (c / W))
  set lam : Fin (Fintype.card (Fin W)) → (Johansson.UpperPair W → ℝ × ℝ) → ℝ :=
    fun i z => BlockBand.Foundations.Spectral.increasingEigenvalue (X z).2 i
  have hlam : ∀ i, Measurable (lam i) := fun i =>
    (BlockBand.Model.Construction.measurable_increasingEigenvalue i).comp hX
  have hpt : ∀ z, -((((Johansson.gaussianMatrix z).1 + F) +
      ((η : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹.trace).im =
        ∑ i, poissonKernel η (lam i z) := by
    intro z
    have h := neg_im_trace_inv_eq_sum_poissonKernel (X z).2 hη
    have e : (Johansson.gaussianMatrix z).1 + F = (X z).1 := add_comm _ _
    rw [e, h]
    rw [← (BlockBand.Foundations.Spectral.increasingIndex).sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [BlockBand.Foundations.Spectral.eigenvalue_increasingIndex]
  simp_rw [hpt]
  have hK : 0 ≤ C / Real.sqrt c * (W : ℝ) := by positivity
  refine lintegral_sum_poissonKernel_le _ lam hlam hK (fun a b hab => ?_) hη
  have h := hC W hW c hc F hF a b hab
  simp_rw [eigenCount_eq_sum_indicator] at h
  exact h

/-- Real and imaginary parts of a matrix with imaginary margin `η`:
`S = F + iY + iη` with `F = (S + Sᴴ)/2`, `Y = (S - Sᴴ)/(2i) - η`. -/
theorem decompose_hasImMargin {n : Type} [Fintype n] [DecidableEq n] {S : Matrix n n ℂ}
    {η : ℝ} (hS : HasImMargin η S) :
    ((1 / 2 : ℂ) • (S + Sᴴ)).IsHermitian ∧
      ((-I / 2) • (S - Sᴴ) - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef ∧
      S = (1 / 2 : ℂ) • (S + Sᴴ) + I • ((-I / 2) • (S - Sᴴ) - (η : ℂ) • (1 : Matrix n n ℂ)) +
        ((η : ℂ) * I) • (1 : Matrix n n ℂ) := by
  have hF : ((1 / 2 : ℂ) • (S + Sᴴ)).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, add_comm]
    ring
  have hΓ : ((-I / 2) • (S - Sᴴ)).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply]
    ring
  have hY : ((-I / 2) • (S - Sᴴ) - (η : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
    refine hΓ.sub ?_
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  refine ⟨hF, Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hY fun v => ?_, ?_⟩
  · have hq : star v ⬝ᵥ (((-I / 2) • (S - Sᴴ) - (η : ℂ) • (1 : Matrix n n ℂ)) *ᵥ v) =
        ((star v ⬝ᵥ (S *ᵥ v)).im : ℂ) - (η : ℂ) * (star v ⬝ᵥ v) := by
      have hstar : star v ⬝ᵥ (Sᴴ *ᵥ v) = star (star v ⬝ᵥ (S *ᵥ v)) := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
        simp only [star_star]
        exact Matrix.star_dotProduct _ _
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub,
        hstar]
      apply Complex.ext
      · simp [Complex.conj_re, Complex.conj_im]
        ring
      · simp [Complex.conj_re, Complex.conj_im]
    rw [hq]
    have hs : (star v ⬝ᵥ v).im = 0 := by
      have := im_star_dotProduct_mulVec_hermitian (Matrix.isHermitian_one (α := ℂ) (n := n)) v
      simpa using this
    rw [Complex.nonneg_iff]
    constructor
    · simp only [sub_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero, hs]
      have := hS v
      linarith
    · simp [hs]
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring_nf
    rw [I_sq]
    ring

/-- **One fresh block against a dissipative background.** Under `GUECountBound C` (`C ≥ 0`),
for `W > 0`, `c > 0`, every deterministic `S` with imaginary margin `η > 0`:
`E[-Im Tr (A + S)⁻¹] ≤ π C/√c · W`, `A ∼ GUE_W(c/W)`. Uniform in `S` and `η`. -/
theorem lintegral_oneBlock_le {C : ℝ} (hC : GUECountBound C) (hC0 : 0 ≤ C) {W : ℕ}
    (hW : 0 < W) {c : ℝ} (hc : 0 < c) {S : Matrix (Fin W) (Fin W) ℂ} {η : ℝ} (hη : 0 < η)
    (hS : HasImMargin η S) :
    ∫⁻ z, ENNReal.ofReal (-(((Johansson.gaussianMatrix z).1 + S)⁻¹.trace).im)
        ∂(Johansson.coordinateMeasure W (Real.toNNReal (c / W))) ≤
      ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * Real.pi) := by
  obtain ⟨hF, hY, hSeq⟩ := decompose_hasImMargin hS
  set F : Matrix (Fin W) (Fin W) ℂ := (1 / 2 : ℂ) • (S + Sᴴ)
  set Y : Matrix (Fin W) (Fin W) ℂ := (-I / 2) • (S - Sᴴ) - (η : ℂ) • 1
  set μ := Johansson.coordinateMeasure W (Real.toNNReal (c / W))
  have : IsProbabilityMeasure μ := Johansson.coordinateMeasure_probability W _
  set Bz : (Johansson.UpperPair W → ℝ × ℝ) → Matrix (Fin W) (Fin W) ℂ :=
    fun z => (Johansson.gaussianMatrix z).1 + F
  have hBz : ∀ z, (Bz z).IsHermitian := fun z => (Johansson.gaussianMatrix z).2.add hF
  set f : (Johansson.UpperPair W → ℝ × ℝ) → ℂ → ℂ := fun z => resolventTrace 1 (Bz z) Y η
  set g : (Johansson.UpperPair W → ℝ × ℝ) → ℝ → ℝ :=
    fun z t => (-Real.pi⁻¹) * ((1 + t ^ 2)⁻¹ * (f z t).im)
  -- the value at `ζ = i`
  have hfI : ∀ z, ((Johansson.gaussianMatrix z).1 + S)⁻¹.trace = f z I := by
    intro z
    simp only [f, resolventTrace, absorbedPencil, Matrix.one_mul, Bz]
    congr 2
    rw [hSeq]
    simp only [F, Y]
    abel
  -- the value on the real axis
  have hft : ∀ z (t : ℝ), f z t = ((((Johansson.gaussianMatrix z).1 + (F + (t : ℂ) • Y)) +
      ((η : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹.trace) := by
    intro z t
    simp only [f, resolventTrace, absorbedPencil, Matrix.one_mul, Bz]
    congr 2
    abel
  have hFt : ∀ t : ℝ, (F + (t : ℂ) • Y).IsHermitian := fun t =>
    hF.add (hY.isHermitian.smul (show IsSelfAdjoint (t : ℂ) from Complex.conj_ofReal t))
  have hnonneg_t : ∀ z (t : ℝ), 0 ≤ -(f z t).im := by
    intro z t
    rw [hft z t, ← add_assoc]
    rw [neg_im_trace_inv_eq_sum_poissonKernel (((Johansson.gaussianMatrix z).2.add hF).add
      (hY.isHermitian.smul (show IsSelfAdjoint (t : ℂ) from Complex.conj_ofReal t))) hη]
    exact Finset.sum_nonneg fun i _ => poissonKernel_nonneg hη _
  have hg_nonneg : ∀ z t, 0 ≤ g z t := by
    intro z t
    have h1 := hnonneg_t z t
    simp only [g]
    have : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    have hpi : 0 ≤ Real.pi⁻¹ := inv_nonneg.mpr Real.pi_pos.le
    nlinarith [mul_nonneg hpi (mul_nonneg this h1)]
  -- Poisson representation for each `z`
  have hpois : ∀ z, Integrable (g z) ∧ ∫ t, g z t = -(f z I).im := by
    intro z
    obtain ⟨hint, heq⟩ := resolventTrace_poisson_im (hBz z) hY hη (1 : Matrix (Fin W) (Fin W) ℂ)
    refine ⟨hint.const_mul _, ?_⟩
    simp only [g]
    rw [integral_const_mul]
    change -Real.pi⁻¹ * ∫ t : ℝ, (1 + t ^ 2)⁻¹ * (resolventTrace 1 (Bz z) Y η t).im = _
    rw [heq]
    field_simp
    rfl
  have hlhs : ∀ z, ENNReal.ofReal (-(((Johansson.gaussianMatrix z).1 + S)⁻¹.trace).im) =
      ∫⁻ t, ENNReal.ofReal (g z t) := by
    intro z
    rw [hfI z, ← (hpois z).2, ofReal_integral_eq_lintegral_ofReal (hpois z).1
      (Filter.Eventually.of_forall (hg_nonneg z))]
  simp_rw [hlhs]
  -- joint measurability
  have hmeasP : Measurable (fun p : (Johansson.UpperPair W → ℝ × ℝ) × ℝ =>
      absorbedPencil (Bz p.1) Y η (p.2 : ℂ)) := by
    rw [Matrix.measurable_iff]
    intro i j
    have h1 : Measurable (fun p : (Johansson.UpperPair W → ℝ × ℝ) × ℝ =>
        (Johansson.gaussianMatrix p.1).1 i j) :=
      ((Matrix.measurable_iff.mp (measurable_gaussianMatrix_val W)) i j).comp measurable_fst
    simp only [absorbedPencil, Bz, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((h1.add measurable_const).add
      ((Complex.measurable_ofReal.comp measurable_snd).mul measurable_const)).add measurable_const
  have hmeasG : Measurable (Function.uncurry fun z t => ENNReal.ofReal (g z t)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have htr : Measurable (fun M : Matrix (Fin W) (Fin W) ℂ => ((1 : Matrix (Fin W) (Fin W) ℂ) *
        M⁻¹).trace) :=
      ((continuous_const.matrix_mul continuous_id).matrix_trace).measurable.comp
        measurable_matrix_inv
    have hf : Measurable (fun p : (Johansson.UpperPair W → ℝ × ℝ) × ℝ => (f p.1 p.2).im) :=
      Complex.measurable_im.comp (htr.comp hmeasP)
    exact measurable_const.mul
      (((measurable_const.add (measurable_snd.pow_const 2)).inv).mul hf)
  rw [lintegral_lintegral_swap hmeasG.aemeasurable]
  -- inner bound for each real `t`
  have hinner : ∀ t : ℝ, ∫⁻ z, ENNReal.ofReal (g z t) ∂μ ≤
      ENNReal.ofReal (Real.pi⁻¹ * (1 + t ^ 2)⁻¹) *
        ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * Real.pi) := by
    intro t
    have hpt : ∀ z, ENNReal.ofReal (g z t) = ENNReal.ofReal (Real.pi⁻¹ * (1 + t ^ 2)⁻¹) *
        ENNReal.ofReal (-((((Johansson.gaussianMatrix z).1 + (F + (t : ℂ) • Y)) +
          ((η : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹.trace).im) := by
      intro z
      rw [← ENNReal.ofReal_mul (by positivity), ← hft z t]
      congr 1
      simp only [g]
      ring
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    exact lintegral_real_background_le hC hC0 hW hc (hFt t) hη
  calc ∫⁻ t, ∫⁻ z, ENNReal.ofReal (g z t) ∂μ
      ≤ ∫⁻ t, ENNReal.ofReal (Real.pi⁻¹ * (1 + t ^ 2)⁻¹) *
          ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * Real.pi) := lintegral_mono hinner
    _ = (∫⁻ t, ENNReal.ofReal (Real.pi⁻¹ * (1 + t ^ 2)⁻¹)) *
          ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * Real.pi) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * Real.pi) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_inv_one_add_sq.const_mul _)
          (Filter.Eventually.of_forall fun t => by positivity), integral_const_mul,
          integral_univ_inv_one_add_sq, inv_mul_cancel₀ Real.pi_pos.ne', ENNReal.ofReal_one,
          one_mul]

end BlockBand.Wegner
