module

public import BlockBand.Critical.Collar.Density.CondSchurWitness

/-!
# Conditional Schur identity: Generic

Part of the proof of the conditional Schur identity in the collar density lemma: the top
density, averaged first over `G`, is exactly `TΣ_F(0)T*`.

`ae_csGeneric_collar`: for `0 < b < 1/2` and every Hermitian `X`, `layerLaw`-a.e. `(A, B)` is
generic (two-stage Fubini, polynomial null sets).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter ProbabilityTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate ComplexOrder ENNReal NNReal

variable {W : ℕ}

/-- Complex matrices (product topology) are second countable (local instance). -/
theorem matrix_secondCountableTopology_gen (ι κ : Type*) [Fintype ι] [Fintype κ] :
    SecondCountableTopology (Matrix ι κ ℂ) :=
  inferInstanceAs (SecondCountableTopology (ι → κ → ℂ))

attribute [local instance] matrix_secondCountableTopology_gen

theorem continuous_blockDiag_gen {k : ℕ} :
    Continuous fun A : Fin k → Matrix (Fin W) (Fin W) ℂ =>
      BlockBand.Internal.Contracts.Layers.blockDiag A := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  unfold BlockBand.Internal.Contracts.Layers.blockDiag
  split_ifs
  · exact (continuous_apply_apply _ _).comp (continuous_apply _)
  · exact continuous_const

theorem continuous_bondMatrix_gen :
    Continuous fun B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ => bondMatrix .common B := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  unfold bondMatrix
  split_ifs
  · exact (continuous_apply_apply _ _).comp ((continuous_apply _).comp (continuous_apply _))
  · exact continuous_const

theorem map_C_map_eval {σ m n : Type} (M : Matrix m n ℂ) (f : σ → ℂ) :
    (M.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)).map (MvPolynomial.eval f) = M := by
  ext i j; simp

/-- **Almost-sure genericity of the collar** (`b > 0`, `b < 1/2`): for `layerLaw`-a.e. `(A, B)`,
no eigenvector of `D = A - e - X` lies in `ker B*`. -/
theorem ae_csGeneric_collar (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    ∀ᵐ ω₁ ∂layerLaw W b .common,
      CsGeneric (collarTopBlock e X ω₁) (bondMatrix .common ω₁.2) := by
  set t := Real.toNNReal ((1 - 2 * b) / W) with htdef
  set t' := Real.toNNReal (b / W) with ht'def
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have ht : (0 : ℝ) < t := by
    rw [htdef, Real.coe_toNNReal _ (div_pos (by linarith) hWr).le]; exact div_pos (by linarith) hWr
  have ht' : t' / 2 ≠ 0 := by
    have : (0 : ℝ) < t' := by
      rw [ht'def, Real.coe_toNNReal _ (div_pos hb0 hWr).le]; exact div_pos hb0 hWr
    intro h
    have h2 : ((t' / 2 : ℝ≥0) : ℝ) = 0 := by rw [h]; rfl
    push_cast at h2
    linarith
  -- the witness
  obtain ⟨l, hl⟩ := (finite_setOf_det_sub_eq_zero (witnessK X)).exists_notMem
  have hl' : (witnessK X - (l : ℂ) • 1).det ≠ 0 := hl
  have h1 : 0 < Real.sqrt ((t : ℝ) / 2) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hAw : BlockBand.Layers.pgBlocksOfCoords W 2 t
      (blockWitness W (l / (Real.sqrt ((t : ℝ) / 2) * (2 / Real.sqrt 2)))) =
      fun k => (if k = 0 then (l : ℂ) else 0) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    funext k
    rw [pgBlocksOfCoords_blockWitness]
    congr 1
    split_ifs
    · have h3 : (Real.sqrt ((t : ℝ) / 2) * (2 / Real.sqrt 2)) *
          (l / (Real.sqrt ((t : ℝ) / 2) * (2 / Real.sqrt 2))) = l := by
        field_simp
      have h4 := congrArg (fun r : ℝ => (r : ℂ)) h3
      push_cast at h4
      rw [← h4]
      push_cast
      ring
    · simp
  set Bw := BlockBand.Layers.bondAssemble (bondWitness W)
  set N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := -((e : ℂ) • 1) - X
  have hDN : ∀ A : Fin 2 → Matrix (Fin W) (Fin W) ℂ,
      BlockBand.Internal.Contracts.Layers.blockDiag A - (e : ℂ) • 1 - X =
        BlockBand.Internal.Contracts.Layers.blockDiag A + N := by
    intro A; simp only [N]; abel
  -- stage A: the end blocks
  have hA : ∀ᵐ A ∂(Measure.pi fun _ : Fin 2 => gueMeasure (Fin W) t),
      (csGram (BlockBand.Internal.Contracts.Layers.blockDiag A - (e : ℂ) • 1 - X)
        (bondMatrix .common Bw)).det ≠ 0 := by
    have hcont : Continuous fun A : Fin 2 → Matrix (Fin W) (Fin W) ℂ =>
        (csGram (BlockBand.Internal.Contracts.Layers.blockDiag A - (e : ℂ) • 1 - X)
          (bondMatrix .common Bw)).det := by
      unfold csGram
      have hD : Continuous fun A : Fin 2 → Matrix (Fin W) (Fin W) ℂ =>
          BlockBand.Internal.Contracts.Layers.blockDiag A - (e : ℂ) • 1 - X :=
        (continuous_blockDiag_gen.sub continuous_const).sub continuous_const
      exact Continuous.matrix_det (continuous_const.add ((hD.matrix_mul continuous_const).matrix_mul
        hD))
    rw [BlockBand.Layers.pi_gueMeasure_eq_map W 2 t, ae_iff]
    simp only [not_not]
    rw [Measure.map_apply (BlockBand.Layers.measurable_pgBlocksOfCoords W 2 t)
        (measurableSet_eq_fun hcont.measurable measurable_const)]
    simp only [Set.preimage, Set.mem_ofPred_eq]
    set BB := bondMatrix .common Bw
    set S := BlockBand.Layers.srecTopPoly W 2 t N
    set Q := BB.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2 × BlockBand.Layers.GaussCoord W) ℂ)
    set R := BBᴴ.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2 × BlockBand.Layers.GaussCoord W) ℂ)
    refine measure_det_eq_zero_of_poly (Q * R + S * (Q * R) * S)
      (fun x => csGram (BlockBand.Internal.Contracts.Layers.blockDiag
        (BlockBand.Layers.pgBlocksOfCoords W 2 t x) - (e : ℂ) • 1 - X) BB) (fun x => ?_)
      (blockWitness W (l / (Real.sqrt ((t : ℝ) / 2) * (2 / Real.sqrt 2)))) ?_
      (BlockBand.Parameters.pi_absolutelyContinuous_volume _
        fun _ => gaussianReal_absolutelyContinuous 0 one_ne_zero)
    · rw [csGram_map, map_C_map_eval, map_C_map_eval, srecTopPoly_map_eval, ← hDN]
      rfl
    · rw [hAw]
      exact det_csGram_witness_ne_zero e hX hl'
  -- stage B: the bonds, for good end blocks
  have hZ : MeasurableSet {ω₁ : LayerSample W .common |
      (csGram (collarTopBlock e X ω₁) (bondMatrix .common ω₁.2)).det = 0} := by
    have hcont : Continuous fun ω₁ : LayerSample W .common =>
        (csGram (collarTopBlock e X ω₁) (bondMatrix .common ω₁.2)).det := by
      unfold csGram collarTopBlock
      have hD : Continuous fun ω₁ : LayerSample W .common =>
          BlockBand.Internal.Contracts.Layers.blockDiag ω₁.1 - (e : ℂ) • 1 - X :=
        ((continuous_blockDiag_gen.comp continuous_fst).sub continuous_const).sub continuous_const
      have hB : Continuous fun ω₁ : LayerSample W .common => bondMatrix .common ω₁.2 :=
        continuous_bondMatrix_gen.comp continuous_snd
      exact Continuous.matrix_det ((hB.matrix_mul hB.matrix_conjTranspose).add
        ((hD.matrix_mul (hB.matrix_mul hB.matrix_conjTranspose)).matrix_mul hD))
    exact measurableSet_eq_fun hcont.measurable measurable_const
  have hnull : layerLaw W b .common {ω₁ : LayerSample W .common |
      (csGram (collarTopBlock e X ω₁) (bondMatrix .common ω₁.2)).det = 0} = 0 := by
    have hlaw : layerLaw W b .common =
        (Measure.pi fun _ : Fin 2 => gueMeasure (Fin W) t).prod
          (BlockBand.Layers.bondLaw 2 1 W t') := rfl
    have : IsProbabilityMeasure (BlockBand.Layers.bondLaw 2 1 W t') := by
      unfold BlockBand.Layers.bondLaw; infer_instance
    rw [hlaw, Measure.prod_apply hZ]
    refine (lintegral_congr_ae ?_).trans (lintegral_zero)
    filter_upwards [hA] with A hAA
    have hmeasB : MeasurableSet {B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ |
        (csGram (BlockBand.Internal.Contracts.Layers.blockDiag A - (e : ℂ) • 1 - X)
          (bondMatrix .common B)).det = 0} := by
      have hB : Continuous fun B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ =>
          bondMatrix .common B := continuous_bondMatrix_gen
      have hcont : Continuous fun B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ =>
          (csGram (BlockBand.Internal.Contracts.Layers.blockDiag A - (e : ℂ) • 1 - X)
            (bondMatrix .common B)).det := by
        unfold csGram
        exact Continuous.matrix_det ((hB.matrix_mul hB.matrix_conjTranspose).add
          ((continuous_const.matrix_mul (hB.matrix_mul hB.matrix_conjTranspose)).matrix_mul
            continuous_const))
      exact measurableSet_eq_fun hcont.measurable measurable_const
    change BlockBand.Layers.bondLaw 2 1 W t' {B | (csGram (collarTopBlock e X (A, B))
      (bondMatrix .common B)).det = 0} = 0
    simp only [collarTopBlock]
    rw [BlockBand.Layers.bondLaw_eq_map, Measure.map_apply BlockBand.Layers.measurable_bondAssemble
      hmeasB]
    set DA := BlockBand.Internal.Contracts.Layers.blockDiag A - (e : ℂ) • 1 - X
    set Dp := DA.map (MvPolynomial.C : ℂ →+* MvPolynomial (BondCoord W) ℂ)
    refine measure_det_eq_zero_of_poly (bondPoly W * bondPolyH W + Dp * (bondPoly W *
      bondPolyH W) * Dp) (fun r => csGram DA (bondMatrix .common (BlockBand.Layers.bondAssemble r)))
      (fun r => ?_) (bondWitness W) hAA (BlockBand.Parameters.pi_absolutelyContinuous_volume _
        fun _ => gaussianReal_absolutelyContinuous 0 ht')
    rw [csGram_map, bondPoly_map_eval, bondPolyH_map_eval, map_C_map_eval]
    rfl
  rw [ae_iff]
  refine measure_mono_null (fun ω₁ hω => ?_) hnull
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hne
  exact hω (csGeneric_of_det_csGram_ne_zero hne)

end BlockBand.Critical.Collar.Density
