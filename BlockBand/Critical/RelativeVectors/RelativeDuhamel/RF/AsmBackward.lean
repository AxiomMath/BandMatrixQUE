module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.AsmFields
public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.Simple
public import BlockBand.Critical.RelativeVectors.AbstractFlow.GeneratorCont
public import BlockBand.Critical.RelativeVectors.AbstractFlow.GeneratorEq

/-!
# The backward field and the mass identity for one simple path

Fix Hermitian `F`, `a < c`, `b₀ > 0`, `ℓ > 0` and a path `ω ∈ simpleRatSet F a c`. Write
`ρ = shortRate`, `κ = refDamping` (continuous on `[a, c]`), `𝓝 = canonFlow a c ρ κ`,
`(K, L) = (refKernel c 𝓝, refFactor c 𝓝)` on the driver space of `dirac ()` (the per-path
reference flow, `isReferenceFlow_canon`), and `(K', L') = (drvKernel K, drvFactor L)` on
`driver × Torus N` with `P' = driverLaw ⊗ Haar`.

* `witnessBackward_eq` (identification by laws): for `s ∈ [a, c]`,
  `g_s(z) = ∫ f(𝓜_{s,c} z + Ξ_{s,c}) d auxLaw` equals `refBackward P' K' L' f s z`. For `s < c`:
  the realization has the law `refKernelLaw a c s ρ κ` of `K_s` (`map_rawKernel`), and `g_s` is
  the integral of a function of `(K, θ, G)` (`integral_prodMap_eq_of_map_eq`,
  `refBackward_drv_eq_integral`). For `s = c`: both sides are `f` (`refSemigroup_terminal`).
* `witness_backward`: the `backward` field. The regularity conjuncts come from the regularity of
  the reference semigroup for `(K', L')` (which is a.s. continuous in `s`); the backward equation
  is `hasDerivAt_symBackward_of_continuousOn`, transported by `symBackward_eq_refBackward`. The
  Euclidean test class is converted by `isC2BoundedBy_of_isArrayC2Bounded`.
* `witness_mass`: `s ↦ E_aux |(𝓜_{s,c})_{kj}|²` is `∫ |(K_s)_{kj}|² d driverLaw` on `[a, c]`
  (phases have modulus `1`), so `mass` and `referenceGenerator_eq_massGenerator` give
  `BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint

open MeasureTheory Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Palm.ReferenceFlow
open BlockBand.Palm.MomentFlow (pathSigma)
open BlockBand.Palm.RelativeLocalization.StochasticBridge

variable {N r : ℕ}

/-- `1 z = z` on arrays. -/
theorem arrayMul_one (z : Fin N → Fin r → ℂ) : arrayMul (1 : Matrix (Fin N) (Fin N) ℂ) z = z :=
  lmul_one' z

section PerPath

variable {F : Matrix (Fin N) (Fin N) ℂ} {a c b₀ : ℝ} {ℓ : ℕ} {ω : FlowSample N}

/-- **Identification of the backward function by equality of laws.** For `s ∈ [a, c]`,
`∫ f(𝓜_{s,c} z + Ξ_{s,c}) d auxLaw = refBackward P' K' L' f s z`, with the symmetrized driver pair
`(K', L')` of `canonFlow`. -/
theorem witnessBackward_eq (hF : F.IsHermitian) (hac : a < c) (hb₀ : 0 < b₀) (hℓ : 0 < ℓ)
    (hω : ω ∈ RelativeDuhamel.simpleRatSet F a c) {C : ℝ} {f : (Fin N → Fin r → ℂ) → ℝ}
    (hf : IsArrayC2Bounded C f) {s : ℝ} (hs : s ∈ Icc a c) :
    (fun z => ∫ ω', f (arrayMul (refM F a c b₀ ℓ ω s c ω') z + refXi F a c b₀ ℓ ω s c ω')
        ∂auxLaw N r) =
      RelativeDuhamel.RF.refBackward ((driverLaw (κ := RotIdx N) (Measure.dirac ())).prod (torusHaar N))
        (drvKernel (refKernel c (canonFlow a c (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ))))
        (drvFactor (refFactor c (canonFlow a c (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ))))
        f s := by
  have hRF := isReferenceFlow_canon hF hac hb₀ hℓ hω
  have hfc : Continuous f := hf.contDiff.continuous
  funext z
  rcases hs.2.lt_or_eq with hsc | hsc
  · have hlaw : (volume : Measure unitInterval).map (rawKernel F a c b₀ ℓ s c ω) =
        (driverLaw (κ := RotIdx N) (Measure.dirac ())).map (refKernel c
          (canonFlow a c (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ)) s) := by
      rw [map_rawKernel hF hac b₀ ℓ hs.1 hsc le_rfl ω, refKernelOf, ite_eq_left hω]
      rfl
    have e1 : ∫ ω', f (arrayMul (refM F a c b₀ ℓ ω s c ω') z + refXi F a c b₀ ℓ ω s c ω')
        ∂auxLaw N r = ∫ x, backIntegrand f z ((rawKernel F a c b₀ ℓ s c ω x.1.1, x.1.2), x.2)
          ∂(((volume : Measure unitInterval).prod (torusHaar N)).prod (matCircularLaw N r)) := rfl
    rw [e1, integral_prodMap_eq_of_map_eq (measurable_rawKernel_left F a c b₀ ℓ s c ω)
      (hRF.measurable_kernel s) hlaw (measurable_backIntegrand hfc z),
      refBackward_drv_eq_integral (hRF.measurable_kernel s) (fun y => rfl) hfc hf.bound z]
  · subst hsc
    have hadm := admissible_of_mem hF hac.le le_rfl hω b₀ ℓ
    have h𝓝 := canonFlow_isRotationFlow hac.le hadm
    rw [← symBackward_eq_refBackward (hRF.measurable_kernel s) (hRF.measurable_factor s) hfc
      hf.bound z]
    simp only [refM_self, refXi_self, add_zero, arrayMul_one, integral_const, probReal_univ,
      one_smul, symBackward, refSemigroup_terminal h𝓝, Function.comp_apply,
      labelPhase_neg_labelPhase]

/-- **The `backward` field of `IsReferenceFlow` for the witness**, on a simple path. -/
theorem witness_backward (hF : F.IsHermitian) (hac : a < c) (hb₀ : 0 < b₀) (hℓ : 0 < ℓ)
    (hω : ω ∈ RelativeDuhamel.simpleRatSet F a c) (C : ℝ) (f : (Fin N → Fin r → ℂ) → ℝ)
    (hf : IsArrayC2Bounded C f) :
    let g : ℝ → (Fin N → Fin r → ℂ) → ℝ :=
      fun s z => ∫ ω', f (arrayMul (refM F a c b₀ ℓ ω s c ω') z + refXi F a c b₀ ℓ ω s c ω')
        ∂auxLaw N r
    (∀ s ∈ Icc a c, IsArrayC2Bounded C (g s)) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => g p.1 p.2) (Icc a c ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (g p.1) p.2) (Icc a c ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (fderiv ℝ (g p.1)) p.2)
      (Icc a c ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
      referenceArrayGenerator F a b₀ ω ℓ p.1 (g p.1) p.2) (Ioo a c ×ˢ univ) ∧
    ∀ z, ∀ s ∈ Ioo a c,
      HasDerivAt (fun s' => g s' z) (-(referenceArrayGenerator F a b₀ ω ℓ s (g s) z)) s := by
  intro g
  set K := refKernel c (canonFlow a c (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ)) with hKdef
  set L := refFactor c (canonFlow a c (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ)) with hLdef
  set P' := (driverLaw (κ := RotIdx N) (Measure.dirac ())).prod (torusHaar N) with hP'def
  set Gd := RelativeDuhamel.RF.refBackward P' (drvKernel K) (drvFactor L) f with hGddef
  have hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow (Measure.dirac ())
      (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c K L :=
    isReferenceFlow_canon hF hac hb₀ hℓ hω
  have hρ := continuousOn_shortRate_of_mem hF hac.le hω ℓ
  have hκ := continuousOn_refDamping_of_mem hF hac.le hω b₀ ℓ
  have hfc : Continuous f := hf.contDiff.continuous
  have hg : ∀ s ∈ Icc a c, g s = Gd s := fun s hs => witnessBackward_eq hF hac hb₀ hℓ hω hf hs
  have hsym : ∀ s, symBackward (Measure.dirac ()) K L f s = Gd s := fun s => funext fun z =>
    symBackward_eq_refBackward (hRF.measurable_kernel s) (hRF.measurable_factor s) hfc hf.bound z
  have hgen : ∀ σ (h : (Fin N → Fin r → ℂ) → ℝ) z, referenceArrayGenerator F a b₀ ω ℓ σ h z =
      refGenerator (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) σ h z :=
    fun σ h z => AbstractFlow.rfGeneratorEq_holds N r F a b₀ ω ℓ σ h z
  
  have hK' : ∀ s, Measurable (drvKernel K s) := fun s => measurable_drvKernel (hRF.measurable_kernel s)
  have hL' : ∀ s, Measurable (drvFactor L s) := fun s => measurable_drvFactor (hRF.measurable_factor s)
  have hfst := Measure.quasiMeasurePreserving_fst (μ := driverLaw (κ := RotIdx N)
    (Measure.dirac ())) (ν := torusHaar N)
  have hcont : ∀ᵐ x ∂P', ContinuousOn (fun s => drvKernel K s x) (Icc a c) ∧
      ContinuousOn (fun s => drvFactor L s x) (Icc a c) := by
    filter_upwards [hfst.ae hRF.continuous, hfst.ae hRF.factor_continuous] with x hx1 hx2
    have h1 := continuous_labelPhaseMatrix_joint.comp_continuousOn
      ((continuousOn_const (c := torusRep x.2)).prodMk hx1)
    have h2 := continuous_rowPhase_joint.comp_continuousOn
      ((continuousOn_const (c := -torusRep x.2)).prodMk hx2)
    exact ⟨h1, h2⟩
  have hcontr : ∀ᵐ x ∂P', ∀ s ∈ Icc a c, ∀ v : Fin N → ℂ,
      l2Norm (drvKernel K s x *ᵥ v) ≤ l2Norm v := by
    filter_upwards [hfst.ae (hRF.contraction 0 fun x _ k => refDamping_nonneg F a b₀ ω ℓ x k)]
      with x hx s hs v
    have h1 : ∀ w : Fin N → ℂ, l2Norm (K s x.1 *ᵥ w) ≤ 1 * l2Norm w := by
      intro w
      have hw := hx s hs w
      rw [zero_mul, neg_zero, Real.exp_zero, one_mul] at hw
      rw [one_mul]
      exact Real.sqrt_le_sqrt hw
    have h2 := l2Norm_labelPhaseMatrix_mulVec_le (α := torusRep x.2) h1 v
    rw [one_mul] at h2
    exact h2
  obtain ⟨hr1, hr2, hr3, hr4⟩ := AbstractFlow.rfBackwardRegular_holds N r _ P' (drvKernel K) (drvFactor L)
    a c hac.le hK' hL' hcont hcontr C f hf
  have hIoo : ∀ s ∈ Ioo a c, s ∈ Icc a c := fun s hs => Ioo_subset_Icc_self hs
  refine ⟨fun s hs => (hg s hs).symm ▸ hr1 s hs, ?_, ?_, ?_, ?_, fun z s hs => ?_⟩
  · exact hr2.congr fun p hp => by simp only [hg p.1 hp.1]; rfl
  · exact hr3.congr fun p hp => by simp only [hg p.1 hp.1]; rfl
  · exact hr4.congr fun p hp => by simp only [hg p.1 hp.1]; rfl
  · have h := AbstractFlow.rfGeneratorContinuous_holds N r _ _ a c hρ hκ Gd hr3 hr4
    refine (h.mono (prod_mono Ioo_subset_Icc_self subset_rfl)).congr fun p hp => ?_
    simp only [hgen, hg p.1 (hIoo p.1 hp.1)]
  · have hJ6 := hasDerivAt_symBackward_of_continuousOn hRF hρ hκ
      (isC2BoundedBy_of_isArrayC2Bounded hf) s hs z
    have hev : (fun s' => g s' z) =ᶠ[𝓝 s] fun s' => symBackward (Measure.dirac ()) K L f s' z := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs'
      rw [hsym s', hg s' (hIoo s' hs')]
    rw [hgen, hg s (hIoo s hs), ← hsym s]
    exact hJ6.congr_of_eventuallyEq hev

/-- **The mass identity for the witness**: `s ↦ E_aux |(𝓜_{s,c})_{kj}|²` solves
`BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c`, on a simple path. -/
theorem witness_mass (hF : F.IsHermitian) (hac : a < c) (hb₀ : 0 < b₀) (hℓ : 0 < ℓ)
    (hω : ω ∈ RelativeDuhamel.simpleRatSet F a c) :
    BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c
      (fun s k j => ∫ ω', ‖refM (r := r) F a c b₀ ℓ ω s c ω' k j‖ ^ 2 ∂auxLaw N r) := by
  have hRF := isReferenceFlow_canon hF hac hb₀ hℓ hω
  rw [referenceGenerator_eq_massGenerator]
  refine backwardPropagator_congr_Icc hac.le hRF.mass fun s hs => ?_
  funext k j
  rcases hs.2.lt_or_eq with hsc | hsc
  · have hlaw : (volume : Measure unitInterval).map (rawKernel F a c b₀ ℓ s c ω) =
        (driverLaw (κ := RotIdx N) (Measure.dirac ())).map (refKernel c
          (canonFlow a c (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ)) s) := by
      rw [map_rawKernel hF hac b₀ ℓ hs.1 hsc le_rfl ω, refKernelOf, ite_eq_left hω]
      rfl
    have hm : Measurable fun M : Matrix (Fin N) (Fin N) ℂ => ‖M k j‖ ^ 2 :=
      ((continuous_norm.pow 2).comp ((continuous_apply j).comp (continuous_apply k))).measurable
    have e1 : ∫ ω', ‖refM (r := r) F a c b₀ ℓ ω s c ω' k j‖ ^ 2 ∂auxLaw N r =
        ∫ t, ‖rawKernel F a c b₀ ℓ s c ω t k j‖ ^ 2 ∂(volume : Measure unitInterval) := by
      simp only [refM, phK, norm_labelPhaseMatrix_apply]
      exact integral_fun_fst_fst _ _ _ (fun t => ‖rawKernel F a c b₀ ℓ s c ω t k j‖ ^ 2)
    rw [e1, ← integral_map (measurable_rawKernel_left F a c b₀ ℓ s c ω).aemeasurable
      hm.aestronglyMeasurable, hlaw,
      integral_map (hRF.measurable_kernel s).aemeasurable hm.aestronglyMeasurable]
  · subst hsc
    simp only [refM_self, hRF.terminal, integral_const, probReal_univ, one_smul]

end PerPath

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
