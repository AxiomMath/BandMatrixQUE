module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.AsmAlg

/-!
# Assembly helpers: the symmetrized pair and change of law

* `phK K θ = P_θ'⁻¹ K P_θ'` and `phL K θ = P_θ'⁻¹ √(1 - KKᴴ)` (`θ'` the representative of the
  torus point `θ`): the symmetrized kernel and factor as functions of `(K, θ)`; both measurable.
* `integral_prodMap_eq_of_map_eq` (**change of law**): for `Ψ` measurable on
  `(Mat × Torus) × ℂ^{N×r}` and `φ₀, φ₁` with the same law,
  `∫ Ψ((φ₀, θ), G) d((μ₀ ⊗ Haar) ⊗ CN) = ∫ Ψ((φ₁, θ), G) d((μ₁ ⊗ Haar) ⊗ CN)`.
* `drvKernel K s (y, θ) = P_θ'⁻¹ K_s(y) P_θ'` and `drvFactor L s (y, θ) = P_θ'⁻¹ L_s(y)`: the
  symmetrized driver pair on `Ωd × Torus N`.
* `symBackward_eq_refBackward`: `symBackward μ K L f s z` equals
  `refBackward (driverLaw μ ⊗ Haar) (drvKernel K) (drvFactor L) f s z` (Fubini in `(y, θ)`).
* `refBackward_drv_eq_integral`: the latter is `∫ Ψ_z((K_s(y), θ), G)` over
  `(driverLaw μ ⊗ Haar) ⊗ CN`, with `Ψ_z((K, θ), G) = f(phK K θ z + phL K θ G)` when
  `L_s = √(1 - K_s K_sᴴ)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint

open MeasureTheory Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.ReferenceFlow
open BlockBand.SourceProcess.FiniteDriverIntegration

variable {N r : ℕ}

attribute [local instance] matrix_secondCountable

/-!
## The symmetrized pair as a function of `(K, θ)`
-/

/-- The symmetrized kernel `P_θ'⁻¹ K P_θ'`. -/
def phK (K : Matrix (Fin N) (Fin N) ℂ) (θ : Torus N) : Matrix (Fin N) (Fin N) ℂ :=
  labelPhaseMatrix (torusRep θ) K

/-- The symmetrized factor `P_θ'⁻¹ √(1 - KKᴴ)`. -/
def phL (K : Matrix (Fin N) (Fin N) ℂ) (θ : Torus N) : Matrix (Fin N) (Fin N) ℂ :=
  rowPhase (-torusRep θ) (sqrtOneSub (K * Kᴴ))

/-- `(β, S) ↦ P_β S` is jointly continuous. -/
theorem continuous_rowPhase_joint :
    Continuous fun q : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℂ => rowPhase q.1 q.2 := by
  refine continuous_matrix fun i j => ?_
  unfold rowPhase
  simp only [Matrix.of_apply]
  fun_prop

/-- `(K, θ) ↦ phK K θ` is measurable. -/
theorem measurable_phK :
    Measurable fun q : Matrix (Fin N) (Fin N) ℂ × Torus N => phK q.1 q.2 :=
  continuous_labelPhaseMatrix_joint.measurable.comp
    ((measurable_torusRep.comp measurable_snd).prodMk measurable_fst)

/-- `K ↦ √(1 - KKᴴ)` is measurable. -/
theorem measurable_sqrtOneSub_mul :
    Measurable fun K : Matrix (Fin N) (Fin N) ℂ => sqrtOneSub (K * Kᴴ) :=
  measurable_sqrtOneSub.comp
    ((continuous_id.mul continuous_id.matrix_conjTranspose).measurable)

/-- `(K, θ) ↦ phL K θ` is measurable. -/
theorem measurable_phL :
    Measurable fun q : Matrix (Fin N) (Fin N) ℂ × Torus N => phL q.1 q.2 :=
  continuous_rowPhase_joint.measurable.comp
    ((measurable_torusRep.comp measurable_snd).neg.prodMk
      (measurable_sqrtOneSub_mul.comp measurable_fst))

/-- The integrand `Ψ_z((K, θ), G) = f(phK K θ z + phL K θ G)` of the backward function. -/
def backIntegrand (f : (Fin N → Fin r → ℂ) → ℝ) (z : Fin N → Fin r → ℂ)
    (x : (Matrix (Fin N) (Fin N) ℂ × Torus N) × (Fin N → Fin r → ℂ)) : ℝ :=
  f (arrayMul (phK x.1.1 x.1.2) z + arrayMul (phL x.1.1 x.1.2) x.2)

/-- `(M, z) ↦ M z` on arrays is jointly continuous. -/
theorem continuous_arrayMul_joint :
    Continuous fun q : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) => arrayMul q.1 q.2 :=
  continuous_lmul_joint

/-- The backward integrand is measurable when `f` is continuous. -/
theorem measurable_backIntegrand {f : (Fin N → Fin r → ℂ) → ℝ} (hf : Continuous f)
    (z : Fin N → Fin r → ℂ) : Measurable (backIntegrand f z) := by
  have hc : Continuous fun q : (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) ×
      (Fin N → Fin r → ℂ) => f (arrayMul q.1.1 z + arrayMul q.1.2 q.2) :=
    hf.comp ((continuous_arrayMul_joint.comp ((continuous_fst.comp continuous_fst).prodMk
      continuous_const)).add (continuous_arrayMul_joint.comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
  have hm : Measurable fun x : (Matrix (Fin N) (Fin N) ℂ × Torus N) × (Fin N → Fin r → ℂ) =>
      ((phK x.1.1 x.1.2, phL x.1.1 x.1.2), x.2) :=
    ((measurable_phK.comp measurable_fst).prodMk (measurable_phL.comp measurable_fst)).prodMk
      measurable_snd
  exact hc.measurable.comp hm

/-!
## Change of law
-/

/-- The image of `(μ ⊗ Haar) ⊗ CN` under `((ω, θ), G) ↦ ((φ ω, θ), G)` is
`((φ_* μ) ⊗ Haar) ⊗ CN`. -/
theorem map_prodMap_prodMap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {φ : Ω → Matrix (Fin N) (Fin N) ℂ} (hφ : Measurable φ) :
    ((μ.prod (torusHaar N)).prod (matCircularLaw N r)).map (Prod.map (Prod.map φ id) id) =
      ((μ.map φ).prod (torusHaar N)).prod (matCircularLaw N r) := by
  have : IsProbabilityMeasure (μ.map φ) := (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).2 inferInstance
  rw [← Measure.map_prod_map _ _ (hφ.prodMap measurable_id) measurable_id,
    ← Measure.map_prod_map _ _ hφ measurable_id, Measure.map_id, Measure.map_id]

/-- The integral of `Ψ((φ ω, θ), G)` against `(μ ⊗ Haar) ⊗ CN` is the integral of `Ψ`
against `((φ_* μ) ⊗ Haar) ⊗ CN`. -/
theorem integral_prodMap_eq_map {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {φ : Ω → Matrix (Fin N) (Fin N) ℂ} (hφ : Measurable φ)
    {Ψ : (Matrix (Fin N) (Fin N) ℂ × Torus N) × (Fin N → Fin r → ℂ) → ℝ} (hΨ : Measurable Ψ) :
    ∫ x, Ψ ((φ x.1.1, x.1.2), x.2) ∂((μ.prod (torusHaar N)).prod (matCircularLaw N r)) =
      ∫ x, Ψ x ∂(((μ.map φ).prod (torusHaar N)).prod (matCircularLaw N r)) := by
  rw [← map_prodMap_prodMap μ hφ,
    integral_map ((hφ.prodMap measurable_id).prodMap measurable_id).aemeasurable
      hΨ.aestronglyMeasurable]
  rfl

/-- **Change of law.** If `φ₀` under `μ₀` and `φ₁` under `μ₁` have the same law, then the
integrals of `Ψ((φ_i, θ), G)` against `(μ_i ⊗ Haar) ⊗ CN` agree, for every measurable `Ψ`. -/
theorem integral_prodMap_eq_of_map_eq {Ω₀ Ω₁ : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    {μ₀ : Measure Ω₀} {μ₁ : Measure Ω₁} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    {φ₀ : Ω₀ → Matrix (Fin N) (Fin N) ℂ} {φ₁ : Ω₁ → Matrix (Fin N) (Fin N) ℂ}
    (h₀ : Measurable φ₀) (h₁ : Measurable φ₁) (hlaw : μ₀.map φ₀ = μ₁.map φ₁)
    {Ψ : (Matrix (Fin N) (Fin N) ℂ × Torus N) × (Fin N → Fin r → ℂ) → ℝ} (hΨ : Measurable Ψ) :
    ∫ x, Ψ ((φ₀ x.1.1, x.1.2), x.2) ∂((μ₀.prod (torusHaar N)).prod (matCircularLaw N r)) =
      ∫ x, Ψ ((φ₁ x.1.1, x.1.2), x.2) ∂((μ₁.prod (torusHaar N)).prod (matCircularLaw N r)) := by
  rw [integral_prodMap_eq_map μ₀ h₀ hΨ, integral_prodMap_eq_map μ₁ h₁ hΨ, hlaw]

/-- The integral of a function of the first coordinate against `(μ ⊗ ν) ⊗ τ`, `ν, τ`
probability measures, is its `μ`-integral. -/
theorem integral_fun_fst_fst {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (τ : Measure γ) [SFinite μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ] (g : α → ℝ) :
    ∫ x, g x.1.1 ∂((μ.prod ν).prod τ) = ∫ y, g y ∂μ := by
  rw [integral_fun_fst (fun x : α × β => g x.1), integral_fun_fst]
  simp only [probReal_univ, one_smul]

/-!
## The symmetrized driver pair
-/

/-- The symmetrized kernel on `Ωd × Torus N`: `K'_s(y, θ) = P_θ'⁻¹ K_s(y) P_θ'`. -/
def drvKernel {Ωd : Type*} (K : ℝ → Ωd → Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (x : Ωd × Torus N) :
    Matrix (Fin N) (Fin N) ℂ :=
  labelPhaseMatrix (torusRep x.2) (K s x.1)

/-- The symmetrized factor on `Ωd × Torus N`: `L'_s(y, θ) = P_θ'⁻¹ L_s(y)`. -/
def drvFactor {Ωd : Type*} (L : ℝ → Ωd → Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (x : Ωd × Torus N) :
    Matrix (Fin N) (Fin N) ℂ :=
  rowPhase (-torusRep x.2) (L s x.1)

/-- The symmetrized kernel is measurable. -/
theorem measurable_drvKernel {Ωd : Type*} [MeasurableSpace Ωd]
    {K : ℝ → Ωd → Matrix (Fin N) (Fin N) ℂ} {s : ℝ} (hK : Measurable (K s)) :
    Measurable (drvKernel K s) :=
  continuous_labelPhaseMatrix_joint.measurable.comp
    ((measurable_torusRep.comp measurable_snd).prodMk (hK.comp measurable_fst))

/-- The symmetrized factor is measurable. -/
theorem measurable_drvFactor {Ωd : Type*} [MeasurableSpace Ωd]
    {L : ℝ → Ωd → Matrix (Fin N) (Fin N) ℂ} {s : ℝ} (hL : Measurable (L s)) :
    Measurable (drvFactor L s) :=
  continuous_rowPhase_joint.measurable.comp
    ((measurable_torusRep.comp measurable_snd).neg.prodMk (hL.comp measurable_fst))

section Driver

variable {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}

/-- The pointwise identity behind `symBackward_eq_refBackward`:
`P_θ'⁻¹ (K (P_θ' z) + L G) = (P_θ'⁻¹ K P_θ') z + (P_θ'⁻¹ L) G`. -/
theorem labelPhase_neg_affine (θ : Fin N → ℝ) (M A : Matrix (Fin N) (Fin N) ℂ)
    (z G : Fin N → Fin r → ℂ) :
    labelPhase (-θ) (lmul M (labelPhase θ z) + lmul A G) =
      arrayMul (labelPhaseMatrix θ M) z + arrayMul (rowPhase (-θ) A) G := by
  rw [labelPhase_add, labelPhase_lmul, neg_neg, labelPhase_neg_labelPhase, arrayMul_rowPhase]
  rfl

/-- **`symBackward` is `refBackward` of the symmetrized driver pair**: for measurable `K_s`, `L_s`
and bounded continuous `f`,
`symBackward μ K L f s z = refBackward (driverLaw μ ⊗ Haar) (drvKernel K) (drvFactor L) f s z`.
Fubini in `(y, θ)`. -/
theorem symBackward_eq_refBackward {s : ℝ} (hK : Measurable (K s)) (hL : Measurable (L s))
    {C : ℝ} {f : (Fin N → Fin r → ℂ) → ℝ} (hfc : Continuous f) (hfb : ∀ z, |f z| ≤ C)
    (z : Fin N → Fin r → ℂ) :
    symBackward μ K L f s z =
      RelativeDuhamel.RF.refBackward ((driverLaw (κ := RotIdx N) μ).prod (torusHaar N)) (drvKernel K)
        (drvFactor L) f s z := by
  set H : DriverSample S (RotIdx N) × Torus N → ℝ := fun x => ∫ G, f (arrayMul (drvKernel K s x) z +
    arrayMul (drvFactor L s x) G) ∂matCircularLaw N r with hH
  have hΦ : Measurable fun q : (DriverSample S (RotIdx N) × Torus N) × (Fin N → Fin r → ℂ) =>
      f (arrayMul (drvKernel K s q.1) z + arrayMul (drvFactor L s q.1) q.2) := by
    have hc : Continuous fun q : (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) ×
        (Fin N → Fin r → ℂ) => f (arrayMul q.1.1 z + arrayMul q.1.2 q.2) :=
      hfc.comp ((continuous_arrayMul_joint.comp ((continuous_fst.comp continuous_fst).prodMk
        continuous_const)).add (continuous_arrayMul_joint.comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
    exact hc.measurable.comp ((((measurable_drvKernel hK).comp measurable_fst).prodMk
      ((measurable_drvFactor hL).comp measurable_fst)).prodMk measurable_snd)
  have hHm : AEStronglyMeasurable H ((driverLaw (κ := RotIdx N) μ).prod (torusHaar N)) :=
    (hΦ.stronglyMeasurable.integral_prod_right' (ν := matCircularLaw N r)).aestronglyMeasurable
  have hHi : Integrable H ((driverLaw (κ := RotIdx N) μ).prod (torusHaar N)) := by
    refine Integrable.of_bound hHm C (Eventually.of_forall fun x => ?_)
    have := norm_integral_le_of_norm_le_const (μ := matCircularLaw N r) (C := C)
      (f := fun G => f (arrayMul (drvKernel K s x) z + arrayMul (drvFactor L s x) G))
      (Eventually.of_forall fun G => by rw [Real.norm_eq_abs]; exact hfb _)
    simpa only [probReal_univ, mul_one] using this
  have e : RelativeDuhamel.RF.refBackward ((driverLaw (κ := RotIdx N) μ).prod (torusHaar N)) (drvKernel K)
      (drvFactor L) f s z = ∫ x, H x ∂((driverLaw (κ := RotIdx N) μ).prod (torusHaar N)) := rfl
  rw [e, integral_prod_symm H hHi]
  unfold symBackward refSemigroup
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun G => ?_)
  simp only [Function.comp_apply, drvKernel, drvFactor]
  rw [labelPhase_neg_affine]

end Driver

/-- **The symmetrized backward function as an integral of `Ψ_z`.** For a pair `(K, L)` on
`Ωd` with `L_s = √(1 - K_s K_sᴴ)`, measurable `K_s` and bounded continuous `f`,
`refBackward (P ⊗ Haar) (drvKernel K) (drvFactor L) f s z = ∫ Ψ_z((K_s y, θ), G)` over
`(P ⊗ Haar) ⊗ CN`. -/
theorem refBackward_drv_eq_integral {Ωd : Type} [MeasurableSpace Ωd] {P : Measure Ωd}
    [IsProbabilityMeasure P] {K L : ℝ → Ωd → Matrix (Fin N) (Fin N) ℂ} {s : ℝ}
    (hK : Measurable (K s)) (hLK : ∀ y, L s y = sqrtOneSub (K s y * (K s y)ᴴ)) {C : ℝ}
    {f : (Fin N → Fin r → ℂ) → ℝ} (hfc : Continuous f) (hfb : ∀ z, |f z| ≤ C)
    (z : Fin N → Fin r → ℂ) :
    RelativeDuhamel.RF.refBackward (P.prod (torusHaar N)) (drvKernel K) (drvFactor L) f s z =
      ∫ x, backIntegrand f z ((K s x.1.1, x.1.2), x.2)
        ∂((P.prod (torusHaar N)).prod (matCircularLaw N r)) := by
  have hL : Measurable (L s) := by
    have e : L s = fun y => sqrtOneSub (K s y * (K s y)ᴴ) := funext hLK
    rw [e]
    exact measurable_sqrtOneSub_mul.comp hK
  rw [AbstractFlow.refBackward_eq_prod (measurable_drvKernel hK) (measurable_drvFactor hL) hfc hfb]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [lmulL_apply, backIntegrand, drvKernel, drvFactor, phK, phL, hLK]
  rfl

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
