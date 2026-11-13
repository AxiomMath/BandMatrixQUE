module

public import BlockBand.Coarea.FixedOmegaCoarea
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalActualPairGoodEventReadback
public import BlockBand.Coarea.Native.BlockBand.Coarea.LagrangeProjectorCorrectness

/-!
# The fresh eigenpair density

The eigenpair Jacobian lemma with a deterministic deformation and an empty exterior block.

## Main results

* `volume_goodSet_fresh_compl`: the fresh good set is conull.
* **`freshDensity_density`**: exactly the field `FreshEigenpairDensityContract.density`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FixedOmega

open Matrix MeasureTheory
open CoareaNative.BlockBand BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
open scoped ENNReal NNReal ComplexConjugate

variable {N : ℕ}

/-- The empty exterior. -/
def emptyExterior : HermitianCoordinateSpace 0 := fun _ => 0

theorem physicalCoareaF_empty (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ) :
    BlockBand.Coarea.physicalCoareaF (hermitianOfFinCoordinates 0 emptyExterior).1
      (0 : Matrix (Fin 0) (Fin N) ℂ) F E = F := by
  unfold BlockBand.Coarea.physicalCoareaF
  simp

theorem physicalCoareaD_empty (E : ℝ) :
    BlockBand.Coarea.physicalCoareaD (hermitianOfFinCoordinates 0 emptyExterior).1
      (0 : Matrix (Fin 0) (Fin N) ℂ) E = 1 := by
  unfold BlockBand.Coarea.physicalCoareaD BlockBand.Coarea.schurClock
    BlockBand.Coarea.physicalCoareaT
  simp

theorem negativeCount_fin_zero (M : Matrix (Fin 0) (Fin 0) ℂ) : negativeCount M = 0 := by
  unfold negativeCount
  split_ifs <;> simp

theorem shiftedInertia_zero (R : HermitianCoordinateSpace 0) (E : ℝ) : shiftedInertia 0 R E = 0 := by
  rw [shiftedInertia_eq_negativeCount, negativeCount_fin_zero]

/-- Every `K` with `K + F` of simple spectrum lies in the fresh good set. -/
theorem mem_goodSet_fresh {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (ℓ : Fin N)
    (K : HermitianCoordinateSpace N)
    (hK : ((hermitianOfFinCoordinates N K).1 + F).charpoly.Separable) :
    K ∈ physicalSelectedSimpleGoodSet ℓ.val emptyExterior (0 : Matrix (Fin 0) (Fin N) ℂ) F := by
  have hMH : ((hermitianOfFinCoordinates N K).1 + F).IsHermitian :=
    (hermitianOfFinCoordinates N K).2.add hF
  set A : HermitianMatrix (Fin N) := ⟨(hermitianOfFinCoordinates N K).1 + F, hMH⟩
  have hinj := orderedEigenvalue_injective_of_separable A hK
  set r : Fin (Fintype.card (Fin N)) := Fin.cast (Fintype.card_fin N).symm ℓ
  set E := orderedEigenvalue A r
  have hMeq : physicalGlobalReducedMatrix emptyExterior (0 : Matrix (Fin 0) (Fin N) ℂ) F K E =
      A.1 := by
    simp [A, physicalGlobalReducedMatrix]
  have hdet : (A.1 - (E : ℂ) • 1).det = 0 :=
    (GaussianRing.det_sub_real_smul_one_eq_zero_iff A E).2 ⟨r, rfl⟩
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hMu : A.1 *ᵥ u = (E : ℂ) • u := by
    have h := hu
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h
  refine ⟨E, fun r' => r'.elim0, u, hu0, by rw [hMeq]; exact hMu, ?_, by rw [hMeq]; exact hMH, ?_⟩
  · intro w hw
    rw [hMeq] at hw
    exact GaussianRing.eigenvector_mem_line_of_orderedEigenvalue_injective A hinj hu0 hMu hw
  · rw [shiftedInertia_zero, zero_add]
    have h := GaussianRing.eigenCount_Iio_orderedEigenvalue_of_injective A hinj r
    have hA : (⟨physicalGlobalReducedMatrix emptyExterior (0 : Matrix (Fin 0) (Fin N) ℂ) F K E,
        by rw [hMeq]; exact hMH⟩ : HermitianMatrix (Fin N)) = A := Subtype.ext hMeq
    rw [hA, h]
    simp [r]

/-- The fresh good set is Lebesgue-conull. -/
theorem volume_goodSet_fresh_compl {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (ℓ : Fin N) :
    volume (physicalSelectedSimpleGoodSet ℓ.val emptyExterior
      (0 : Matrix (Fin 0) (Fin N) ℂ) F)ᶜ = 0 := by
  set f := finCoords N F
  have hf : (hermitianOfFinCoordinates N f).1 = F := hermitianOfFinCoordinates_finCoords hF
  have hsub : (physicalSelectedSimpleGoodSet ℓ.val emptyExterior
      (0 : Matrix (Fin 0) (Fin N) ℂ) F)ᶜ ⊆
      (fun K => K + f) ⁻¹' (hermitianSimpleSpectrumCoordinates N)ᶜ := by
    intro K hK
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    intro hS
    apply hK
    apply mem_goodSet_fresh hF ℓ K
    have hadd : (hermitianOfFinCoordinates N (K + f)).1 =
        (hermitianOfFinCoordinates N K).1 + F := by
      rw [← hf]
      exact congrArg Subtype.val ((hermitianFinCoordinatesLinearEquiv N).map_add K f)
    have := hS
    unfold hermitianSimpleSpectrumCoordinates at this
    simp only [Set.mem_ofPred_eq] at this
    rwa [hadd] at this
  refine measure_mono_null hsub ?_
  rw [measure_preimage_add_right]
  exact volume_hermitianSimpleSpectrumCoordinates_compl N

/-- **The fresh eigenpair density** (the field `FreshEigenpairDensityContract.density`; the second
claim of the coarea theorem at a fixed deformation, via the eigenpair Jacobian lemma), with
exactly the type of that field. -/
theorem freshDensity_density : ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ),
    F.IsHermitian → ∀ (t : ℝ≥0), 0 < t → ∀ (ℓ : Fin N)
    (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ), IsFreshFrame U →
    ∀ g : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞, Measurable g →
      (∫⁻ G, g G ∂gueMeasure (Fin N) t) =
        ∫⁻ E : ℝ, freshEigenpairFiber F t ℓ U E (fun _ G => g G) := by
  intro N hN F hF t ht ℓ U hU g hg
  have hd : 1 ≤ N := hN
  rw [lintegral_gueMeasure_eq_finFiber hd ℓ.val emptyExterior (0 : Matrix (Fin 0) (Fin N) ℂ) hF
    ht hU.1 (fun v hv => hU.2 v hv) hg (volume_goodSet_fresh_compl hF ℓ)]
  unfold finFiber freshEigenpairFiber
  refine lintegral_congr fun E => ?_
  have hne : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine lintegral_congr_ae ?_
  filter_upwards [ProjectiveHaar.ae_l2Norm_projectiveHaar (Fin N)] with v hv
  refine lintegral_congr fun G' => ?_
  have hvv : (star v ⬝ᵥ v).re = 1 := by
    rw [← l2Norm_sq_eq_re, hv, one_pow]
  simp only [physicalCoareaF_empty, physicalCoareaD_empty, Matrix.one_mulVec, hvv, mul_one,
    negativeCount_fin_zero, add_zero]
  rfl

end BlockBand.Coarea.FixedOmega
