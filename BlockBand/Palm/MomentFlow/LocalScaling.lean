module

public import BlockBand.Palm.MomentFlow.BridgeLaw
public import BlockBand.Internal.Contracts.Inputs

/-!
# The Gaussian source law and `gueMeasure` (scaling)

* `map_hermCoords_coordinateMeasure`: the Johansson coordinate law (independent upper pairs; real
  diagonal `N(0,t)`, real and imaginary upper parts `N(0,t/2)`, a dummy diagonal imaginary
  coordinate at `0`) maps to the coordinate product `hermCoordGaussian N t`.
* `map_gaussianMatrixRaw`: `(Johansson.coordinateMeasure N t).map gaussianMatrixRaw =
  gueMeasure (Fin N) t`.
* `gueMeasure_map_smul`: `(gueMeasure (Fin N) t).map (c • ·) = gueMeasure (Fin N) (c² t)`.
* **`map_gueSourceLaw_smul`**: for `σ ≥ 0`, `(gueSourceLaw N).map (W ↦ √σ W) =
  gueMeasure (Fin N) (σ/N)`; in particular the law of `flowMatrix F a ω σ - F` under `flowLaw N a`
  is the law of `√σ W`, `W ~ gueSourceLaw N` (`map_flowMatrix_sub_eq_gueSourceLaw`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.Coarea.GUELaw
open CoareaNative.BlockBand (StrictUpperIndex HermitianCoordinate hermitianMatrixOfCoordinates
  hermitianUpperEntry)
open scoped NNReal ENNReal

variable {N : ℕ}

/-- Diagonal / real-upper / imaginary-upper coordinates of a Johansson coordinate vector. -/
def hermCoordsOfUpper (z : Johansson.UpperPair N → ℝ × ℝ) : HermitianCoordinate N → ℝ
  | .inl i => (z ⟨(i, i), le_rfl⟩).1
  | .inr (.inl ij) => (z ⟨ij.1, ij.2.le⟩).1
  | .inr (.inr ij) => (z ⟨ij.1, ij.2.le⟩).2

theorem measurable_hermCoordsOfUpper : Measurable (hermCoordsOfUpper (N := N)) := by
  refine measurable_pi_iff.2 fun k => ?_
  rcases k with i | ij | ij
  · exact measurable_fst.comp (measurable_pi_apply _)
  · exact measurable_fst.comp (measurable_pi_apply _)
  · exact measurable_snd.comp (measurable_pi_apply _)

theorem gaussianMatrixRaw_eq (z : Johansson.UpperPair N → ℝ × ℝ) :
    Johansson.gaussianMatrixRaw z = hermitianMatrixOfCoordinates (hermCoordsOfUpper z) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Johansson.gaussianMatrixRaw, hermitianMatrixOfCoordinates, hermCoordsOfUpper]
  · by_cases hlt : i < j
    · simp [Johansson.gaussianMatrixRaw, hermitianMatrixOfCoordinates, hermCoordsOfUpper,
        hermitianUpperEntry, Johansson.complexPair, hij, hlt, hlt.le]
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      have hle : ¬ i ≤ j := fun h => hlt (lt_of_le_of_ne h hij)
      simp [Johansson.gaussianMatrixRaw, hermitianMatrixOfCoordinates, hermCoordsOfUpper,
        hermitianUpperEntry, Johansson.complexPair, hij, hlt, hle]

/-- Upper pairs are diagonal indices or strict-upper indices. -/
def upperPairEquiv (N : ℕ) : Johansson.UpperPair N ≃ Fin N ⊕ StrictUpperIndex N where
  toFun p := if h : p.1.1 = p.1.2 then .inl p.1.1 else .inr ⟨p.1, lt_of_le_of_ne p.2 h⟩
  invFun
    | .inl i => ⟨(i, i), le_rfl⟩
    | .inr ij => ⟨ij.1, ij.2.le⟩
  left_inv p := by
    by_cases h : p.1.1 = p.1.2
    · simp only [h, ↓reduceDIte]
      apply Subtype.ext; ext <;> simp [h]
    · simp [h]
  right_inv k := by
    rcases k with i | ij
    · simp
    · simp [ij.2.ne]

instance (t : ℝ≥0) (q : Johansson.UpperPair N) :
    IsProbabilityMeasure (Johansson.upperEntryMeasure t q) :=
  Johansson.upperEntryMeasure_probability t q

/-- The Johansson coordinate law maps to the coordinate product `hermCoordGaussian N t`. -/
theorem map_hermCoords_coordinateMeasure (t : ℝ≥0) :
    (Johansson.coordinateMeasure N t).map hermCoordsOfUpper = hermCoordGaussian N t := by
  unfold hermCoordGaussian
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_hermCoordsOfUpper (MeasurableSet.univ_pi hs)]
  -- the preimage is a box
  set S : Johansson.UpperPair N → Set (ℝ × ℝ) := fun p =>
    if h : p.1.1 = p.1.2 then Prod.fst ⁻¹' s (.inl p.1.1)
    else s (.inr (.inl ⟨p.1, lt_of_le_of_ne p.2 h⟩)) ×ˢ s (.inr (.inr ⟨p.1, lt_of_le_of_ne p.2 h⟩))
  have hpre : hermCoordsOfUpper ⁻¹' (univ.pi s) = univ.pi S := by
    ext z
    simp only [mem_preimage, mem_univ_pi]
    constructor
    · intro hz p
      by_cases h : p.1.1 = p.1.2
      · have := hz (.inl p.1.1)
        simp only [S, h, ↓reduceDIte, mem_preimage]
        have hp : p = ⟨(p.1.1, p.1.1), le_rfl⟩ := by
          apply Subtype.ext; ext <;> simp [h]
        rw [hp]; exact this
      · simp only [S, h, ↓reduceDIte, mem_prod]
        exact ⟨hz (.inr (.inl ⟨p.1, _⟩)), hz (.inr (.inr ⟨p.1, _⟩))⟩
    · intro hz k
      rcases k with i | ij | ij
      · have := hz ⟨(i, i), le_rfl⟩
        simpa [S, hermCoordsOfUpper] using this
      · have := hz ⟨ij.1, ij.2.le⟩
        simp only [S, ij.2.ne, ↓reduceDIte, mem_prod] at this
        exact this.1
      · have := hz ⟨ij.1, ij.2.le⟩
        simp only [S, ij.2.ne, ↓reduceDIte, mem_prod] at this
        exact this.2
  rw [hpre, Johansson.coordinateMeasure, Measure.pi_pi]
  -- the product over upper pairs
  have hfac : ∀ p, Johansson.upperEntryMeasure t p (S p) =
      match upperPairEquiv N p with
      | .inl i => gaussianReal 0 (hermCoordVariance t (.inl i)) (s (.inl i))
      | .inr ij => gaussianReal 0 (hermCoordVariance t (.inr (.inl ij))) (s (.inr (.inl ij))) *
          gaussianReal 0 (hermCoordVariance t (.inr (.inr ij))) (s (.inr (.inr ij))) := by
    intro p
    by_cases h : p.1.1 = p.1.2
    · have he : upperPairEquiv N p = .inl p.1.1 := by simp [upperPairEquiv, h]
      rw [he]
      simp only [S, h, ↓reduceDIte, Johansson.upperEntryMeasure, ↓reduceIte, hermCoordVariance]
      rw [Measure.map_apply (by fun_prop) (measurable_fst (hs _))]
      congr 1
    · have he : upperPairEquiv N p = .inr ⟨p.1, lt_of_le_of_ne p.2 h⟩ := by
        simp [upperPairEquiv, h]
      rw [he]
      simp only [S, h, ↓reduceDIte, Johansson.upperEntryMeasure, ↓reduceIte, hermCoordVariance]
      rw [Measure.prod_prod]
  simp_rw [hfac]
  rw [← (upperPairEquiv N).symm.prod_comp]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type, Finset.prod_mul_distrib]

/-- **The Gaussian matrix `gaussianMatrixRaw` has law** `GUE_N(t)`. -/
theorem map_gaussianMatrixRaw (t : ℝ≥0) :
    (Johansson.coordinateMeasure N t).map Johansson.gaussianMatrixRaw = gueMeasure (Fin N) t := by
  have e : (Johansson.gaussianMatrixRaw (N := N)) =
      hermitianMatrixOfCoordinates ∘ hermCoordsOfUpper := funext gaussianMatrixRaw_eq
  rw [e, ← Measure.map_map (measurable_hermitianMatrixOfCoordinates N)
    measurable_hermCoordsOfUpper, map_hermCoords_coordinateMeasure,
    gueMeasure_eq_map_hermitianMatrixOfCoordinates]

theorem measurable_matrix_const_smul (c : ℂ) :
    Measurable (fun M : Matrix (Fin N) (Fin N) ℂ => c • M) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact measurable_const.mul (measurable_matrixEntry i j)

/-- `(GUE(t)).map (c • ·) = GUE(c² t)`. -/
theorem gueMeasure_map_smul (t : ℝ≥0) (c : ℝ) :
    (gueMeasure (Fin N) t).map (fun M => (c : ℂ) • M) =
      gueMeasure (Fin N) (Real.toNNReal (c ^ 2) * t) := by
  rw [gueMeasure_eq_map_coords, Measure.map_map (measurable_matrix_const_smul _)
    measurable_gueOfCoords]
  have e : ((fun M : Matrix (Fin N) (Fin N) ℂ => (c : ℂ) • M) ∘ gueOfCoords N) =
      gueOfCoords N ∘ (fun r => c • r) := by
    funext r; simp [gueOfCoords_smul]
  rw [e, ← Measure.map_map measurable_gueOfCoords (measurable_const_smul _),
    pi_gaussian_map_smul, gueMeasure_eq_map_coords]

/-- `√σ W` with `W ~ gueSourceLaw N` has law `GUE_N(σ/N)`. -/
theorem map_gueSourceLaw_smul {σ : ℝ} (hσ : 0 ≤ σ) :
    (gueSourceLaw N).map (fun W : CEH.SourceHermitian N => ((Real.sqrt σ : ℝ) : ℂ) • W.1) =
      gueMeasure (Fin N) (Real.toNNReal (σ / N)) := by
  have hm : Measurable (fun W : CEH.SourceHermitian N => ((Real.sqrt σ : ℝ) : ℂ) • W.1) :=
    (measurable_matrix_const_smul _).comp measurable_subtype_coe
  have hg : Measurable (fun z : Johansson.UpperPair N → ℝ × ℝ =>
      (⟨(Johansson.gaussianMatrix z).1, (Johansson.gaussianMatrix z).2⟩ :
        CEH.SourceHermitian N)) :=
    (measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix).subtype_mk
  unfold gueSourceLaw
  rw [Measure.map_map hm hg]
  have e : ((fun W : CEH.SourceHermitian N => ((Real.sqrt σ : ℝ) : ℂ) • W.1) ∘
      fun z : Johansson.UpperPair N → ℝ × ℝ =>
        (⟨(Johansson.gaussianMatrix z).1, (Johansson.gaussianMatrix z).2⟩ :
          CEH.SourceHermitian N)) =
      (fun M => ((Real.sqrt σ : ℝ) : ℂ) • M) ∘ Johansson.gaussianMatrixRaw := rfl
  have hraw : Measurable (Johansson.gaussianMatrixRaw (N := N)) :=
    measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix
  rw [e, ← Measure.map_map (measurable_matrix_const_smul _) hraw, map_gaussianMatrixRaw,
    gueMeasure_map_smul]
  congr 1
  ext
  simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast,
    Real.sq_sqrt hσ, Real.coe_toNNReal']
  rw [max_eq_left hσ, max_eq_left (div_nonneg hσ (Nat.cast_nonneg N))]
  ring

/-- The marginal of the flow is `F + √σ W`, `W ~ gueSourceLaw N`. -/
theorem map_flowMatrix_sub_eq_gueSourceLaw (F : Matrix (Fin N) (Fin N) ℂ) {a σ : ℝ}
    (ha : 0 ≤ a) (haσ : a ≤ σ) :
    (flowLaw N a).map (fun ω => flowMatrix F a ω σ - F) =
      (gueSourceLaw N).map (fun W : CEH.SourceHermitian N => ((Real.sqrt σ : ℝ) : ℂ) • W.1) := by
  rw [map_flowMatrix_sub F ha haσ, map_gueSourceLaw_smul (by linarith)]

/-- Probabilities of matrix events along the flow are `gueSourceLaw` probabilities of the CEH matrix
`√σ W` (the form in which `ExternalLocalGUE`'s bad events are stated). -/
theorem flowLaw_preimage_eq_gueSourceLaw (F : Matrix (Fin N) (Fin N) ℂ) {a σ : ℝ}
    (ha : 0 ≤ a) (haσ : a ≤ σ) {S : Set (Matrix (Fin N) (Fin N) ℂ)} (hS : MeasurableSet S) :
    flowLaw N a {ω | flowMatrix F a ω σ - F ∈ S} =
      gueSourceLaw N {W | ((Real.sqrt σ : ℝ) : ℂ) • W.1 ∈ S} := by
  have h := congrArg (fun μ => μ S) (map_flowMatrix_sub_eq_gueSourceLaw F ha haσ)
  have hg : Measurable (fun ω : FlowSample N => flowMatrix F a ω σ - F) := by
    have := measurable_matrix_sub.comp ((measurable_flowMatrix F a σ).prodMk
      (measurable_const (a := F)))
    simpa only [Function.comp_def] using this
  have hm : Measurable (fun W : CEH.SourceHermitian N => ((Real.sqrt σ : ℝ) : ℂ) • W.1) :=
    (measurable_matrix_const_smul _).comp measurable_subtype_coe
  rw [Measure.map_apply hg hS, Measure.map_apply hm hS] at h
  exact h

end BlockBand.Palm.MomentFlow
