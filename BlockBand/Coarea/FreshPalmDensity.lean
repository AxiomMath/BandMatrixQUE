module

public import BlockBand.Coarea.FreshPalmDensityLaw
public import BlockBand.Coarea.FreshPalmDensityContinuity
public import BlockBand.Coarea.FixedOmegaFresh
public import BlockBand.Palm.ScalarGaussianWeight

/-!
# `FreshEigenpairDensityContract`: the scalar Palm weight is the fresh eigenpair density

Proves the field `palm` and then the whole statement
`BlockBand.Internal.Contracts.CoareaPalm.FreshEigenpairDensityContract`. The scalar Palm weight
is the one of the fresh Palm theorem; it is identified with the eigenpair density used in the
physical angular theorem.

*Measures.* `A⁰ ~ freshTracelessLaw N c₀` (traceless part of `GUE_N(c₀/N)`), Lebesgue `dE`,
`ν_N = projectiveHaar (Fin N)`, `GUE_{N-1}(c₀/N)`; the scalar `ζ ~ N(0, c₀/N²)`.
*Domain.* every `N ≥ 1`, Hermitian `F`, `c₀ > 0`, zero-based rank `ℓ`, measurable frame `U`
(`IsFreshFrame`), measurable `f ≥ 0` of the eigenprojector, **every** `E ∈ ℝ`. Exact
identity of extended nonnegative reals; no limit, norm or uniformity statement.

## Proof

1. *Scalar split* (`scalarShiftLaw_fin_eq_gueMeasure`): `GUE_N(t) = law(A⁰ + ζ I)`, `t = c₀/N`,
   `ζ ~ N(0, t/N) = N(0, c₀/N²)` independent of `A⁰`. For Hermitian traceless `A⁰`,
   `λ_ℓ(F + A⁰ + ζ) = ν⁰_ℓ + ζ` and `tracelessPart (A⁰ + ζ) = A⁰`.
2. *Integrated identity* (`lintegral_mul_palmSide_eq`): for measurable `h ≥ 0` on `ℝ`, the test
   `g(G) = h(λ_ℓ(F + G)) f(P_ℓ(F + G⁰))` gives, by the scalar kernel
   (`BlockBand.Palm.lintegral_dependentScalarShift_eq_kernel`),
   `∫ g dGUE_N(t) = ∫ dE h(E) E_{A⁰}[w_{ℓ,E} f(P_ℓ)]`, and by `freshDensity_density` together
   with the rank identification on the fiber support (`freshReconstructed_rank`:
   `λ_ℓ(F + G_rec) = E`, eigenprojector of `F + G_rec - cI` equal to `vv*`),
   `∫ g dGUE_N(t) = ∫ dE h(E) fiber_E(f(vv*))`. Hence the two sides agree for a.e. `E`.
3. *Every `E`* (bounded `f`): both sides are continuous in `E` (dominated convergence;
   `continuous_freshEigenpairFiber` and `continuous_palmSide`), so a.e. equality is equality.
4. *General `f`*: monotone convergence along `min(f, n)`.

## Main results

* **`freshDensity_palm`**: exactly the field `FreshEigenpairDensityContract.palm`.
* **`freshEigenpairDensityContract_holds : FreshEigenpairDensityContract`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FreshPalm

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw BlockBand.Coarea.FixedOmega
  BlockBand.Coarea.PoleExclusion BlockBand.Model.Construction
open scoped ENNReal NNReal ComplexConjugate

variable {N : ℕ}

/-!
## Spectral and trace bookkeeping
-/

/-- The selected eigenprojector `u_ℓ u_ℓ*` of `K`. -/
def freshProjector (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  vecMulVec (freshEigenvector K ℓ) (star (freshEigenvector K ℓ))

theorem measurable_freshProjector (ℓ : Fin N) :
    Measurable fun K : Matrix (Fin N) (Fin N) ℂ => freshProjector K ℓ := by
  apply Measurable.of_eval_matrix
  intro a b
  simp only [freshProjector, freshEigenvector, vecMulVec_apply, Pi.star_apply]
  exact (measurable_rawOrderedColumnSelection _ a).mul
    (Complex.continuous_conj.measurable.comp (measurable_rawOrderedColumnSelection _ b))

theorem measurable_freshEigenvalue (ℓ : Fin N) :
    Measurable fun K : Matrix (Fin N) (Fin N) ℂ => freshEigenvalue K ℓ :=
  measurable_rawIncreasingEigenvalue _

theorem measurable_vecMulVec_self :
    Measurable fun v : Fin N → ℂ => vecMulVec v (star v) := by
  apply Measurable.of_eval_matrix
  intro a b
  simp only [vecMulVec_apply, Pi.star_apply]
  exact (measurable_pi_apply a).mul (Complex.continuous_conj.measurable.comp (measurable_pi_apply b))

/-- `λ_ℓ(K + ζ) = λ_ℓ(K) + ζ` for Hermitian `K`. -/
theorem freshEigenvalue_add_smul_one {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (ζ : ℝ) (ℓ : Fin N) :
    freshEigenvalue (K + (ζ : ℂ) • 1) ℓ = freshEigenvalue K ℓ + ζ := by
  have heq : K - ((-ζ : ℝ) : ℂ) • 1 = K + (ζ : ℂ) • 1 := by
    rw [Complex.ofReal_neg, neg_smul, sub_neg_eq_add]
  have hK' : (K + (ζ : ℂ) • 1).IsHermitian := by
    rw [← heq]; exact hK.sub (isHermitian_one.smul (Complex.conj_ofReal _))
  have h := CoareaNative.BlockBand.orderedEigenvalue_sub_real_smul_one ⟨K, hK⟩ (-ζ)
    (Fin.cast (Fintype.card_fin N).symm ℓ)
  simp only at h
  have hsub : (⟨K - ((-ζ : ℝ) : ℂ) • 1, hK.sub (isHermitian_one.smul (RCLike.conj_ofReal _))⟩ :
      CoareaNative.BlockBand.HermitianMatrix (Fin N)) = ⟨K + (ζ : ℂ) • 1, hK'⟩ := Subtype.ext heq
  rw [hsub, sub_neg_eq_add] at h
  unfold freshEigenvalue
  rw [rawIncreasingEigenvalue_eq _ _ hK', rawIncreasingEigenvalue_eq _ _ hK]
  exact h

theorem trace_tracelessPart (hN : 0 < N) (G : Matrix (Fin N) (Fin N) ℂ) :
    (tracelessPart G).trace = 0 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold tracelessPart
  rw [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
  field_simp
  ring

theorem tracelessPart_add_smul_one (hN : 0 < N) {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.trace = 0) (ζ : ℝ) : tracelessPart (A + (ζ : ℂ) • 1) = A := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold tracelessPart
  rw [trace_add, hA, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, zero_add]
  have : ((N : ℂ))⁻¹ * ((ζ : ℂ) * (N : ℂ)) = ζ := by field_simp
  rw [this, add_sub_cancel_right]

/-- For Hermitian `G`, `F + G⁰ = F + G - c I` with the real scalar `c = Tr G / N`. -/
theorem add_tracelessPart_eq (F : Matrix (Fin N) (Fin N) ℂ) {G : Matrix (Fin N) (Fin N) ℂ}
    (hG : G.IsHermitian) :
    F + tracelessPart G = F + G - ((((N : ℂ))⁻¹ * G.trace).re : ℂ) • 1 := by
  have htr : star G.trace = G.trace := by rw [← Matrix.trace_conjTranspose, hG.eq]
  have hreal : ((((N : ℂ))⁻¹ * G.trace).re : ℂ) = ((N : ℂ))⁻¹ * G.trace := by
    apply Complex.conj_eq_iff_re.mp
    change star ((((N : ℂ))⁻¹ * G.trace)) = _
    rw [star_mul', htr]
    congr 1
    simp
  rw [hreal]
  unfold tracelessPart
  rw [Fintype.card_fin]
  abel

theorem freshReconstructed_isHermitian (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (E : ℝ) (v : Fin N → ℂ)
    {G' : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ} (hG' : G'.IsHermitian) :
    (freshReconstructed U F E v G').IsHermitian := by
  unfold freshReconstructed
  exact (((vecMulVec_self_isHermitian v).smul (Complex.conj_ofReal E)).add
    (isHermitian_mul_mul_conjTranspose (U v)
      ((isHermitian_conjTranspose_mul_mul (U v) hF).add hG'))).sub hF

/-!
## The two sides as functions of `E`
-/

/-- Left side of `palm`: `E_{A⁰}[w_{ℓ,E} f(u_ℓu_ℓ*)]`. -/
def palmSide (F : Matrix (Fin N) (Fin N) ℂ) (c₀ : ℝ) (ℓ : Fin N)
    (f : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞) (E : ℝ) : ℝ≥0∞ :=
  ∫⁻ A0, ENNReal.ofReal (palmWeight F c₀ E ℓ A0) * f (freshProjector (F + A0) ℓ)
    ∂freshTracelessLaw N c₀

/-- Right side of `palm`: the fresh fiber density at `E` tested against `f(vv*)`. -/
def fiberSide (F : Matrix (Fin N) (Fin N) ℂ) (c₀ : ℝ) (ℓ : Fin N)
    (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ)
    (f : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞) (E : ℝ) : ℝ≥0∞ :=
  freshEigenpairFiber F (Real.toNNReal (c₀ / N)) ℓ U E (fun v _ => f (vecMulVec v (star v)))

instance isProbabilityMeasure_freshTracelessLaw (c₀ : ℝ) :
    IsProbabilityMeasure (freshTracelessLaw N c₀) := by
  unfold freshTracelessLaw
  exact (Measure.isProbabilityMeasure_map_iff measurable_tracelessPart.aemeasurable).2
    inferInstance

theorem ae_freshTracelessLaw (hN : 0 < N) (c₀ : ℝ) :
    ∀ᵐ A0 ∂freshTracelessLaw N c₀, A0.IsHermitian ∧ A0.trace = 0 := by
  unfold freshTracelessLaw
  have hS : MeasurableSet {A : Matrix (Fin N) (Fin N) ℂ | A.IsHermitian ∧ A.trace = 0} :=
    (measurableSet_isHermitian (Fin N)).inter
      (measurableSet_eq_fun (continuous_id.matrix_trace).measurable measurable_const)
  rw [ae_map_iff measurable_tracelessPart.aemeasurable hS]
  filter_upwards [ae_isHermitian_gueMeasure (ι := Fin N) _] with G hG
  exact ⟨tracelessPart_isHermitian hG, trace_tracelessPart hN G⟩

theorem measurable_palmWeight (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N) :
    Measurable fun A0 => palmWeight F c₀ E ℓ A0 := by
  unfold palmWeight BlockBand.Palm.scalarWeight
  exact (measurable_gaussianPDFReal _ _).comp
    (measurable_const.sub ((measurable_freshEigenvalue ℓ).comp
      (measurable_matrix_add measurable_const measurable_id)))

theorem continuous_palmWeight_E (F : Matrix (Fin N) (Fin N) ℂ) (c₀ : ℝ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) : Continuous fun E => palmWeight F c₀ E ℓ A0 := by
  unfold palmWeight BlockBand.Palm.scalarWeight
  rw [gaussianPDFReal_def]
  fun_prop

/-- **Continuity of the Palm side** for a bounded observable. -/
theorem continuous_palmSide (F : Matrix (Fin N) (Fin N) ℂ) (c₀ : ℝ) (ℓ : Fin N)
    {f : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hfC : ∀ M, f M ≤ C) : Continuous (palmSide F c₀ ℓ f) := by
  rw [continuous_iff_continuousAt]
  intro E₀
  set B : ℝ := (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))⁻¹
  have hfP : Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ => f (freshProjector (F + A0) ℓ) :=
    hf.comp ((measurable_freshProjector ℓ).comp (measurable_matrix_add measurable_const
      measurable_id))
  refine tendsto_lintegral_filter_of_dominated_convergence
    (F := fun E A0 => ENNReal.ofReal (palmWeight F c₀ E ℓ A0) * f (freshProjector (F + A0) ℓ))
    (f := fun A0 => ENNReal.ofReal (palmWeight F c₀ E₀ ℓ A0) * f (freshProjector (F + A0) ℓ))
    (fun _ => ENNReal.ofReal B * C)
    (Eventually.of_forall fun E =>
      (ENNReal.measurable_ofReal.comp (measurable_palmWeight F c₀ E ℓ)).mul hfP) ?_ ?_ ?_
  · exact Eventually.of_forall fun E => Eventually.of_forall fun A0 =>
      mul_le_mul' (ENNReal.ofReal_le_ofReal (BlockBand.Palm.scalarWeight_le_prefactor _ _ _ _))
        (hfC _)
  · rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  · exact Eventually.of_forall fun A0 => ENNReal.Tendsto.mul_const
      ((ENNReal.continuous_ofReal.tendsto _).comp
        ((continuous_palmWeight_E F c₀ ℓ A0).tendsto E₀))
      (Or.inr (ne_top_of_le_ne_top hC (hfC _)))

/-!
## The integrated identity
-/

theorem measurable_fiberKernel_slice {U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ}
    (hU : Measurable U) (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (ℓ : Fin N) (E : ℝ)
    (v : Fin N → ℂ) :
    Measurable fun G' : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ => fiberKernel U F t ℓ E v G' := by
  have h := (measurable_fiberKernel hU F t ℓ E).comp (measurable_prodMk_left (x := v))
  exact h

theorem freshEigenpairFiber_eq_general (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (ℓ : Fin N)
    (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ) (E : ℝ)
    (g : (Fin N → ℂ) → Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞) :
    freshEigenpairFiber F t ℓ U E g =
      ∫⁻ v, ∫⁻ G', fiberKernel U F t ℓ E v G' * g v (freshReconstructed U F E v G')
        ∂gueMeasure (Fin (N - 1)) t ∂projectiveHaar (Fin N) := rfl

section Integrated

variable (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {c₀ : ℝ}
  (hc₀ : 0 < c₀) (ℓ : Fin N) {U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ}
  (hU : IsFreshFrame U) {f : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞} (hf : Measurable f)

include hN hF hU hf in
/-- The fiber of the test `g(G) = h(λ_ℓ(F+G)) f(P_ℓ(F + G⁰))` is `h(E) · fiberSide(E)`. -/
theorem fiber_test_eq (h : ℝ → ℝ≥0∞) (t : ℝ≥0) (E : ℝ) :
    freshEigenpairFiber F t ℓ U E (fun _ G =>
        h (freshEigenvalue (F + G) ℓ) * f (freshProjector (F + tracelessPart G) ℓ)) =
      h E * freshEigenpairFiber F t ℓ U E (fun v _ => f (vecMulVec v (star v))) := by
  have hne : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [freshEigenpairFiber_eq_general, freshEigenpairFiber_eq]
  have hφ : Measurable fun v : Fin N → ℂ => f (vecMulVec v (star v)) :=
    hf.comp measurable_vecMulVec_self
  have hjoint : Measurable fun p : (Fin N → ℂ) × Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ =>
      fiberKernel U F t ℓ E p.1 p.2 * f (vecMulVec p.1 (star p.1)) :=
    (measurable_fiberKernel hU.1 F t ℓ E).mul (hφ.comp measurable_fst)
  calc (∫⁻ v, ∫⁻ G', fiberKernel U F t ℓ E v G' *
          (h (freshEigenvalue (F + freshReconstructed U F E v G') ℓ) *
            f (freshProjector (F + tracelessPart (freshReconstructed U F E v G')) ℓ))
          ∂gueMeasure (Fin (N - 1)) t ∂projectiveHaar (Fin N))
      = ∫⁻ v, ∫⁻ G', h E * (fiberKernel U F t ℓ E v G' * f (vecMulVec v (star v)))
          ∂gueMeasure (Fin (N - 1)) t ∂projectiveHaar (Fin N) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ProjectiveHaar.ae_l2Norm_projectiveHaar (Fin N)] with v hv
        refine lintegral_congr_ae ?_
        filter_upwards [ae_isHermitian_gueMeasure (ι := Fin (N - 1)) t] with G' hG'
        by_cases hk : fiberKernel U F t ℓ E v G' = 0
        · rw [hk]; simp
        · have hcnt : negativeCount (freshFrameM U F E v G') = ℓ.val := by
            by_contra hc; apply hk; simp [fiberKernel, hc]
          have hdet : (freshFrameM U F E v G').det ≠ 0 := by
            intro hd; apply hk; simp [fiberKernel, hd]
          have h0 := (freshReconstructed_rank hN U hU hF E v hv G' hG' hdet ℓ hcnt 0).1
          have hGh := freshReconstructed_isHermitian U hF E v hG'
          have h1 := (freshReconstructed_rank hN U hU hF E v hv G' hG' hdet ℓ hcnt
            (((N : ℂ))⁻¹ * (freshReconstructed U F E v G').trace).re).2
          simp only [Complex.ofReal_zero, zero_smul, sub_zero, sub_zero] at h0
          rw [h0, freshProjector, add_tracelessPart_eq F hGh, h1]
          ring
    _ = h E * ∫⁻ v, ∫⁻ G', fiberKernel U F t ℓ E v G' * f (vecMulVec v (star v))
          ∂gueMeasure (Fin (N - 1)) t ∂projectiveHaar (Fin N) := by
        rw [← lintegral_const_mul _ hjoint.lintegral_prod_right']
        refine lintegral_congr fun v => ?_
        exact lintegral_const_mul _ ((measurable_fiberKernel_slice hU.1 F t ℓ E v).mul_const _)

include hN hF hc₀ hU hf in
/-- **Integrated identity**: `∫ dE h(E) palmSide(E) = ∫ dE h(E) fiberSide(E)`. -/
theorem lintegral_mul_palmSide_eq {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ E, h E * palmSide F c₀ ℓ f E = ∫⁻ E, h E * fiberSide F c₀ ℓ U f E := by
  set t : ℝ≥0 := Real.toNNReal (c₀ / N)
  set c₀' : ℝ≥0 := Real.toNNReal c₀
  set σ : ℝ≥0 := BlockBand.Palm.scalarVariance c₀' N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : 0 < t := Real.toNNReal_pos.2 (div_pos hc₀ hNr)
  have hc₀' : c₀' ≠ 0 := (Real.toNNReal_pos.2 hc₀).ne'
  have hσ : (σ : ℝ) = (t : ℝ) / N := by
    rw [BlockBand.Palm.coe_scalarVariance, Real.coe_toNNReal _ hc₀.le,
      Real.coe_toNNReal _ (div_pos hc₀ hNr).le]
    field_simp
  set g : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞ := fun G =>
    h (freshEigenvalue (F + G) ℓ) * f (freshProjector (F + tracelessPart G) ℓ)
  have hadd : ∀ {α : Type} [MeasurableSpace α] {k : α → Matrix (Fin N) (Fin N) ℂ},
      Measurable k → Measurable fun x => F + k x := fun hk =>
    measurable_matrix_add measurable_const hk
  have hg : Measurable g :=
    (hh.comp ((measurable_freshEigenvalue ℓ).comp (hadd measurable_id))).mul
      (hf.comp ((measurable_freshProjector ℓ).comp (hadd measurable_tracelessPart)))
  -- fiber side
  have hR : ∫⁻ G, g G ∂gueMeasure (Fin N) t = ∫⁻ E, h E * fiberSide F c₀ ℓ U f E := by
    rw [freshDensity_density N hN F hF t ht ℓ U hU g hg]
    refine lintegral_congr fun E => ?_
    exact fiber_test_eq hN hF ℓ hU hf h t E
  -- Palm side
  set μ0 := freshTracelessLaw N c₀
  have hμ0 : μ0 = (gueMeasure (Fin N) t).map tracelessPart := rfl
  set ν : Matrix (Fin N) (Fin N) ℂ → ℝ := fun A0 => freshEigenvalue (F + A0) ℓ
  have hν : Measurable ν := (measurable_freshEigenvalue ℓ).comp (hadd measurable_id)
  set Φ : Matrix (Fin N) (Fin N) ℂ × ℝ → ℝ≥0∞ := fun p => h p.2 * f (freshProjector (F + p.1) ℓ)
  have hΦ : Measurable Φ :=
    (hh.comp measurable_snd).mul (hf.comp ((measurable_freshProjector ℓ).comp
      (hadd measurable_fst)))
  have hL : ∫⁻ G, g G ∂gueMeasure (Fin N) t = ∫⁻ E, h E * palmSide F c₀ ℓ f E := by
    rw [← scalarShiftLaw_fin_eq_gueMeasure hN t σ hσ]
    unfold scalarShiftLaw
    rw [lintegral_map hg measurable_scalarAdd, ← hμ0]
    have hcongr : (fun y : Matrix (Fin N) (Fin N) ℂ × ℝ => g (y.1 + (y.2 : ℂ) • 1)) =ᵐ[μ0.prod
        (gaussianReal 0 σ)] fun y => Φ (y.1, ν y.1 + y.2) := by
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ0)
        (ν := gaussianReal 0 σ)).ae (ae_freshTracelessLaw hN c₀)] with y hy
      simp only [g, Φ, ν]
      rw [tracelessPart_add_smul_one hN hy.2, ← add_assoc,
        freshEigenvalue_add_smul_one (hF.add hy.1)]
    rw [lintegral_congr_ae hcongr,
      BlockBand.Palm.lintegral_dependentScalarShift_eq_kernel μ0 hc₀' hN.ne' hν hΦ]
    refine lintegral_congr fun E => ?_
    have hfP : Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ =>
        ENNReal.ofReal (palmWeight F c₀ E ℓ A0) * f (freshProjector (F + A0) ℓ) :=
      (ENNReal.measurable_ofReal.comp (measurable_palmWeight F c₀ E ℓ)).mul
        (hf.comp ((measurable_freshProjector ℓ).comp (hadd measurable_id)))
    unfold palmSide
    rw [← lintegral_const_mul _ hfP]
    refine lintegral_congr fun A0 => ?_
    simp only [Φ, ν, BlockBand.Palm.scalarWeightENN_eq_ofReal]
    unfold palmWeight
    ring
  rw [← hL, hR]

end Integrated

/-!
## Every `E`
-/

theorem setLIntegral_eq_lintegral_indicator_mul {S : Set ℝ} (hS : MeasurableSet S)
    (φ : ℝ → ℝ≥0∞) : ∫⁻ x in S, φ x = ∫⁻ x, S.indicator 1 x * φ x := by
  rw [← lintegral_indicator hS]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ S <;> simp [hx]

/-- Bounded observables: equality for every `E`. -/
theorem palmSide_eq_fiberSide_of_bounded (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {c₀ : ℝ} (hc₀ : 0 < c₀) (ℓ : Fin N)
    {U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ} (hU : IsFreshFrame U)
    {f : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hfC : ∀ M, f M ≤ C) : palmSide F c₀ ℓ f = fiberSide F c₀ ℓ U f := by
  have hLc := continuous_palmSide F c₀ ℓ hf hC hfC
  have hRc : Continuous (fiberSide F c₀ ℓ U f) :=
    continuous_freshEigenpairFiber hN hF _ ℓ hU (hf.comp measurable_vecMulVec_self) hC
      (fun v => hfC _)
  refine (Continuous.ae_eq_iff_eq volume hLc hRc).1 ?_
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hLc.measurable hRc.measurable ?_
  intro S hS _
  rw [setLIntegral_eq_lintegral_indicator_mul hS, setLIntegral_eq_lintegral_indicator_mul hS]
  exact lintegral_mul_palmSide_eq hN hF hc₀ ℓ hU hf (measurable_one.indicator hS)

theorem iSup_min_natCast (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by
  show ⨆ n : ℕ, a ⊓ (n : ℝ≥0∞) = a
  rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]

theorem palmSide_eq_iSup (F : Matrix (Fin N) (Fin N) ℂ) (c₀ : ℝ) (ℓ : Fin N)
    {f : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞} (hf : Measurable f) (E : ℝ) :
    palmSide F c₀ ℓ f E = ⨆ n : ℕ, palmSide F c₀ ℓ (fun M => min (f M) n) E := by
  unfold palmSide
  rw [← lintegral_iSup]
  · refine lintegral_congr fun A0 => ?_
    rw [← ENNReal.mul_iSup, iSup_min_natCast]
  · intro n
    exact (ENNReal.measurable_ofReal.comp (measurable_palmWeight F c₀ E ℓ)).mul
      ((hf.comp ((measurable_freshProjector ℓ).comp (measurable_matrix_add measurable_const
        measurable_id))).min measurable_const)
  · intro m n hmn A0
    exact mul_le_mul' le_rfl (min_le_min_left _ (by exact_mod_cast hmn))

theorem fiberSide_eq_iSup (F : Matrix (Fin N) (Fin N) ℂ) (c₀ : ℝ) (ℓ : Fin N)
    {U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ} (hU : Measurable U)
    {f : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞} (hf : Measurable f) (E : ℝ) :
    fiberSide F c₀ ℓ U f E = ⨆ n : ℕ, fiberSide F c₀ ℓ U (fun M => min (f M) n) E := by
  have hK : Measurable fun p : (Fin N → ℂ) × Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ =>
      fiberKernel U F (Real.toNNReal (c₀ / N)) ℓ E p.1 p.2 :=
    measurable_fiberKernel hU F _ ℓ E
  have hW : Measurable fun v => ∫⁻ G', fiberKernel U F (Real.toNNReal (c₀ / N)) ℓ E v G'
      ∂gueMeasure (Fin (N - 1)) (Real.toNNReal (c₀ / N)) :=
    hK.lintegral_prod_right'
  have hside : ∀ φ : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞, fiberSide F c₀ ℓ U φ E =
      ∫⁻ v, (∫⁻ G', fiberKernel U F (Real.toNNReal (c₀ / N)) ℓ E v G'
        ∂gueMeasure (Fin (N - 1)) (Real.toNNReal (c₀ / N))) * φ (vecMulVec v (star v))
        ∂projectiveHaar (Fin N) := by
    intro φ
    unfold fiberSide
    rw [freshEigenpairFiber_eq]
    refine lintegral_congr fun v => ?_
    exact lintegral_mul_const _ (measurable_fiberKernel_slice hU F _ ℓ E v)
  simp_rw [hside]
  rw [← lintegral_iSup]
  · refine lintegral_congr fun v => ?_
    rw [← ENNReal.mul_iSup, iSup_min_natCast]
  · intro n
    exact hW.mul ((hf.comp measurable_vecMulVec_self).min measurable_const)
  · intro m n hmn v
    exact mul_le_mul' le_rfl (min_le_min_left _ (by exact_mod_cast hmn))

/-- **`FreshEigenpairDensityContract.palm`**: exactly the field type. -/
theorem freshDensity_palm : ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ),
    F.IsHermitian → ∀ (c₀ : ℝ), 0 < c₀ → ∀ (ℓ : Fin N)
    (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ), IsFreshFrame U →
    ∀ f : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞, Measurable f →
      ∀ E : ℝ, (∫⁻ A0, ENNReal.ofReal (palmWeight F c₀ E ℓ A0) *
            f (vecMulVec (freshEigenvector (F + A0) ℓ) (star (freshEigenvector (F + A0) ℓ)))
          ∂freshTracelessLaw N c₀) =
        freshEigenpairFiber F (Real.toNNReal (c₀ / N)) ℓ U E
          (fun v _ => f (vecMulVec v (star v))) := by
  intro N hN F hF c₀ hc₀ ℓ U hU f hf E
  change palmSide F c₀ ℓ f E = fiberSide F c₀ ℓ U f E
  rw [palmSide_eq_iSup F c₀ ℓ hf, fiberSide_eq_iSup F c₀ ℓ hU.1 hf]
  congr 1
  funext n
  have hb := palmSide_eq_fiberSide_of_bounded hN hF hc₀ ℓ hU (hf.min measurable_const)
    (C := (n : ℝ≥0∞)) (ENNReal.natCast_ne_top n) (fun M => min_le_right _ _)
  exact congrFun hb E

/-- **`FreshEigenpairDensityContract`** holds. -/
theorem freshEigenpairDensityContract_holds : FreshEigenpairDensityContract where
  frame_exists := BlockBand.Coarea.ContractClauses.freshDensity_frame_exists
  density := BlockBand.Coarea.FixedOmega.freshDensity_density
  palm := freshDensity_palm

end BlockBand.Coarea.FreshPalm
