module

public import BlockBand.Window.Count.SharperFreshCount
public import BlockBand.Counting.NativeCountTransport
public import BlockBand.Counting.SpectralScaling

/-!
# `GueWindowFactorialBound` from PSSS and a one-block law identification

* `gueSample_scale`, `gueMeasure_scale`: `GUE_W(c/W)` is the image of `GUE_W(1/W)` under
  `B ↦ √c B`.
* `windowCount_eq_eigenCount`: `windowCount η M = PSSS.eigenCount ⟨M⟩ [-η, η]`.
* `GueNativeLaw` — the remaining **law identification** (no estimate): for every `W ≥ 1`
  there is a one-block `PSSS.BlockGUE.Law` (block size `W`, variance `1/W`) and an
  index equivalence under which its matrix has law `gueMeasure (Fin W) (1/W)`. Not an
  assumption of any finished result.
* `gueWindowFactorialBound_of`: `NativeInputs.psss` (the PSSS source contract) and
  `GueNativeLaw` give `GueWindowFactorialBound` with `C = psss.C`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory ProbabilityTheory Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open BlockBand.External BlockBand.External.PSSS BlockBand.Counting
open scoped ENNReal NNReal

theorem gueSample_scale {ι : Type*} (c : ℝ) (hc : 0 < c) (W : ℕ) (X : ι × ι → ℂ) :
    gueSample (Real.toNNReal (c / W)) X =
      ((Real.sqrt c : ℝ) : ℂ) • gueSample (Real.toNNReal (1 / W)) X := by
  ext a b
  simp only [gueSample, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  have : (c / W / 2 : ℝ) = c * (1 / W / 2) := by ring
  rw [this, Real.sqrt_mul hc.le, Complex.ofReal_mul, mul_assoc]

theorem gueMeasure_scale {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 < c) (W : ℕ) :
    gueMeasure ι (Real.toNNReal (c / W)) =
      (gueMeasure ι (Real.toNNReal (1 / W))).map
        (fun B : Matrix ι ι ℂ => ((Real.sqrt c : ℝ) : ℂ) • B) := by
  unfold gueMeasure
  rw [Measure.map_map (continuous_const_smul _).measurable (continuous_gueSample' _).measurable]
  congr 1
  funext X
  exact gueSample_scale c hc W X

theorem windowCount_eq_eigenCount {ι : Type*} [Fintype ι] [DecidableEq ι] (η : ℝ)
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    windowCount η M = eigenCount ⟨M, hM⟩ (Icc (-η) η) := by
  classical
  unfold windowCount eigenCount
  simp only [hM, ↓reduceDIte]
  rw [Finset.card_filter, Finset.card_filter,
    ← Equiv.sum_comp BlockBand.Foundations.Spectral.increasingIndex]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BlockBand.Foundations.Spectral.eigenvalue_increasingIndex]
  simp only [Set.mem_Icc, abs_le]

/-- One block of size `W`. -/
abbrev oneBlockSizes (W : ℕ) : Fin 1 → ℕ := fun _ => W

/-- **One-block law identification (remaining obligation 1').** For every `W ≥ 1` there is
a PSSS one-block law `M` (block size `W`, entry variance `1/W`) and an index
equivalence `e` such that `reindex e e (M.G)` has law `gueMeasure (Fin W) (1/W)` under
`M.P`. Pure Gaussian law identification; no estimate. Not an assumption of any finished
result. -/
def GueNativeLaw : Prop :=
  ∀ (W : ℕ) (hW : 0 < W), ∃ (M : BlockGUE.Law.{0} (oneBlockSizes W) (fun _ => hW))
    (e : BlockGUE.Index (oneBlockSizes W) ≃ Fin W),
    IdentDistrib (fun ω => Matrix.reindex e e (M.G ω)) id M.P
      (gueMeasure (Fin W) (Real.toNNReal (1 / W)))

/-- **Single-block window factorial moments from PSSS.** Dependencies: the PSSS source
contract (`NativeInputs.psss`, constant `C = psss.C`) and the law identification
`GueNativeLaw`. Conclusion `GueWindowFactorialBound`: law `gueMeasure (Fin W) (c/W)`, every
`c > 0`, `W ≥ 1`, Hermitian `F` (no norm bound), `η > 0`, `r ≥ 1`. -/
theorem gueWindowFactorialBound_of (psss : PSSS.SourceContract.{0}) (hL : GueNativeLaw) :
    GueWindowFactorialBound := by
  refine ⟨psss.C, psss.C_pos, ?_⟩
  intro c hc W hW F hF η hη r hr
  obtain ⟨M, e, hid⟩ := hL W hW
  set s : ℝ := Real.sqrt c with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hc
  have hg : Measurable (fun B : Matrix (Fin W) (Fin W) ℂ =>
      ((windowCount η (B + F)).descFactorial r : ℝ)) :=
    (measurable_from_nat (f := fun n : ℕ => (n.descFactorial r : ℝ))).comp
      ((measurable_windowCount η).comp (measurable_id.add_const _))
  rw [gueMeasure_scale c hc W, integral_map (continuous_const_smul _).measurable.aemeasurable
    hg.aestronglyMeasurable]
  have hcomp := (hid.comp (hg.comp (continuous_const_smul ((s : ℝ) : ℂ)).measurable)).integral_eq
  simp only [Function.comp_def, id] at hcomp
  rw [← hcomp]
  -- the deformation in coordinates
  set A₀ : HermitianMatrix (BlockGUE.Index (oneBlockSizes W)) :=
    hermitianReindex e.symm ⟨((s⁻¹ : ℝ) : ℂ) • F, hF.smul (by simp [IsSelfAdjoint])⟩ with hA₀
  have hpt : ∀ ω, windowCount η (((s : ℝ) : ℂ) • Matrix.reindex e e (M.G ω) + F) =
      BlockGUE.intervalCount M A₀ (Icc (-η / s) (η / s)) ω := by
    intro ω
    set K := hermitianReindex e (BlockGUE.deformed M A₀ ω) with hK
    have hKeq : ((s : ℝ) : ℂ) • Matrix.reindex e e (M.G ω) + F = ((s : ℝ) : ℂ) • K.1 := by
      ext x y
      simp only [hK, hermitianReindex, BlockGUE.deformed, hA₀, Matrix.reindex_apply,
        Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Equiv.symm_symm, Equiv.apply_symm_apply]
      rw [mul_add, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne', Complex.ofReal_one,
        one_mul, add_comm]
    have hsK : (((s : ℝ) : ℂ) • K.1).IsHermitian := K.2.smul (by simp [IsSelfAdjoint])
    rw [hKeq, windowCount_eq_eigenCount η _ hsK]
    unfold BlockGUE.intervalCount
    rw [← nativeEigenCount_hermitianReindex e (BlockGUE.deformed M A₀ ω), ← hK]
    rw [nativeEigenCount_eq_orderedEigenvalueCount, nativeEigenCount_eq_orderedEigenvalueCount]
    have := orderedEigenvalueCount_positiveScale_Icc K.2 s hs hsK (-η / s) (η / s)
    rw [mul_div_cancel₀ _ hs.ne', mul_div_cancel₀ _ hs.ne'] at this
    exact this
  simp_rw [hpt]
  have hb := psss.factorialBound (fun _ => hW) M A₀ (-η / s) (η / s)
    (by apply div_le_div_of_nonneg_right _ hs.le; linarith) r hr
  unfold FactorialMomentBound factorialCount at hb
  refine hb.trans (le_of_eq ?_)
  rw [blockGUE_dimension]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  congr 1
  field_simp
  ring

end BlockBand.Window.Count
