module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.AsmLaw
public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.Kernel
public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.LawConv
public import BlockBand.Palm.ReferenceFlowExist
public import BlockBand.GaussianCalculus.MultivariateCircularIBP

/-!
# The reference-flow witness `(Ω_aux, P_aux, 𝓜, Ξ)`

* `realize F a c b₀ ℓ s u`: for `a ≤ s ≤ u ≤ c`, a chosen realization
  (`exists_refKernel_realization`, with `refKernelLawContinuity`) of the kernel law
  `refKernelOf … s u` on `unitInterval`; the constant `0` otherwise.
* `rawKernel … s u ω t`: `1` if `s = u`, else `realize … s u ω t`.
* `AuxSample N r = (unitInterval × Torus N) × ℂ^{N×r}` with
  `auxLaw N r = (Lebesgue ⊗ Haar) ⊗ CN` (a probability measure).
* `refM … ω s u ((t, θ), G) = P_θ'⁻¹ K P_θ'` and `refXi … ω s u ((t, θ), G) = P_θ'⁻¹ √(1 - KKᴴ) G`,
  with `K = rawKernel … s u ω t` (`phK`, `phL`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint

open MeasureTheory Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.Stochastic
open BlockBand.Palm.ReferenceFlow
open BlockBand.Palm.MomentFlow (pathSigma)
open BlockBand.Palm.RelativeLocalization.StochasticBridge
open scoped NNReal

variable {N r : ℕ}

/-!
## The realization of the kernel law
-/

open Classical in
/-- A chosen realization of `refKernelOf F a c b₀ ℓ s u` on `unitInterval` when
`F` is Hermitian, `a < c` and `a ≤ s ≤ u ≤ c`; the constant `0` otherwise. -/
def realize (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (s u : ℝ) :
    FlowSample N → unitInterval → Matrix (Fin N) (Fin N) ℂ :=
  if h : F.IsHermitian ∧ a < c ∧ a ≤ s ∧ s ≤ u ∧ u ≤ c then
    Classical.choose (exists_refKernel_realization (refKernelLawContinuity N) h.1 h.2.1 b₀ ℓ
      h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else fun _ _ => 0

/-- The properties of the realization `realize` in the range `a ≤ s ≤ u ≤ c`. -/
theorem realize_spec {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (hac : a < c)
    (b₀ : ℝ) (ℓ : ℕ) {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (huc : u ≤ c) :
    Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace unitInterval)]
      (fun p : FlowSample N × unitInterval => realize F a c b₀ ℓ s u p.1 p.2) ∧
    (∀ ω, volume.map (realize F a c b₀ ℓ s u ω) = refKernelOf F a c b₀ ℓ s u ω) ∧
    ∀ ω t (v : Fin N → ℂ), l2Norm (realize F a c b₀ ℓ s u ω t *ᵥ v) ≤
      Real.exp (-(b₀ * N * (u - s) / (2 * ℓ))) * l2Norm v := by
  have h : F.IsHermitian ∧ a < c ∧ a ≤ s ∧ s ≤ u ∧ u ≤ c := ⟨hF, hac, has, hsu, huc⟩
  rw [realize, dite_eq_left_of_eq_true (eq_true h)]
  exact Classical.choose_spec (exists_refKernel_realization (refKernelLawContinuity N) h.1 h.2.1
    b₀ ℓ h.2.2.1 h.2.2.2.1 h.2.2.2.2)

/-- `realize` is jointly measurable for every `s, u` (constant outside the range). -/
theorem measurable_realize (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (s u : ℝ) :
    Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace unitInterval)]
      (fun p : FlowSample N × unitInterval => realize F a c b₀ ℓ s u p.1 p.2) := by
  by_cases h : F.IsHermitian ∧ a < c ∧ a ≤ s ∧ s ≤ u ∧ u ≤ c
  · exact (realize_spec h.1 h.2.1 b₀ ℓ h.2.2.1 h.2.2.2.1 h.2.2.2.2).1
  · have e : realize F a c b₀ ℓ s u = fun _ _ => 0 := by
      simp only [realize, h, dite_false]
    rw [e]
    exact measurable_const

open Classical in
/-- The kernel before symmetrization: `1` if `s = u`, else `realize … s u ω t`. -/
def rawKernel (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (s u : ℝ) (ω : FlowSample N)
    (t : unitInterval) : Matrix (Fin N) (Fin N) ℂ :=
  if s = u then 1 else realize F a c b₀ ℓ s u ω t

/-- `rawKernel` is jointly measurable for every `s, u`. -/
theorem measurable_rawKernel (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (s u : ℝ) :
    Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace unitInterval)]
      (fun p : FlowSample N × unitInterval => rawKernel F a c b₀ ℓ s u p.1 p.2) := by
  by_cases h : s = u
  · have e : (fun p : FlowSample N × unitInterval => rawKernel F a c b₀ ℓ s u p.1 p.2) =
        fun _ => 1 := by
      funext p
      simp only [rawKernel, h, ite_true]
    rw [e]
    exact measurable_const
  · have e : (fun p : FlowSample N × unitInterval => rawKernel F a c b₀ ℓ s u p.1 p.2) =
        fun p => realize F a c b₀ ℓ s u p.1 p.2 := by
      funext p
      simp only [rawKernel, h, ite_false]
    rw [e]
    exact measurable_realize F a c b₀ ℓ s u

/-- For each path `ω`, `t ↦ rawKernel … s u ω t` is measurable. -/
theorem measurable_rawKernel_left (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (s u : ℝ)
    (ω : FlowSample N) : Measurable (rawKernel F a c b₀ ℓ s u ω) := by
  let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
  have h : Measurable (Function.uncurry (rawKernel F a c b₀ ℓ s u)) :=
    measurable_rawKernel F a c b₀ ℓ s u
  exact h.of_uncurry_left

/-- **Contraction of `rawKernel`** for `a ≤ s ≤ u ≤ c`, every path and every `t`. -/
theorem rawKernel_contracts {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    (hac : a < c) (b₀ : ℝ) (ℓ : ℕ) {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (huc : u ≤ c)
    (ω : FlowSample N) (t : unitInterval) (v : Fin N → ℂ) :
    l2Norm (rawKernel F a c b₀ ℓ s u ω t *ᵥ v) ≤
      Real.exp (-(b₀ * N * (u - s) / (2 * ℓ))) * l2Norm v := by
  by_cases h : s = u
  · simp only [rawKernel, h, ite_true, Matrix.one_mulVec, sub_self, mul_zero, zero_div, neg_zero,
      Real.exp_zero, one_mul, le_refl]
  · simp only [rawKernel, h, ite_false]
    exact (realize_spec hF hac b₀ ℓ has hsu huc).2.2 ω t v

/-- **Law of `rawKernel`** for `a ≤ s < u ≤ c`: the kernel law `refKernelOf`. -/
theorem map_rawKernel {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (hac : a < c)
    (b₀ : ℝ) (ℓ : ℕ) {s u : ℝ} (has : a ≤ s) (hsu : s < u) (huc : u ≤ c) (ω : FlowSample N) :
    volume.map (rawKernel F a c b₀ ℓ s u ω) = refKernelOf F a c b₀ ℓ s u ω := by
  have e : rawKernel F a c b₀ ℓ s u ω = realize F a c b₀ ℓ s u ω := by
    funext t
    simp only [rawKernel, hsu.ne, ite_false]
  rw [e]
  exact (realize_spec hF hac b₀ ℓ has hsu.le huc).2.1 ω

/-!
## The auxiliary space and the witness
-/

/-- The auxiliary sample space `(unitInterval × Torus N) × ℂ^{N×r}`. -/
abbrev AuxSample (N r : ℕ) := (unitInterval × Torus N) × (Fin N → Fin r → ℂ)

/-- The auxiliary law `(Lebesgue ⊗ Haar) ⊗ CN`. -/
def auxLaw (N r : ℕ) : Measure (AuxSample N r) :=
  ((volume : Measure unitInterval).prod (torusHaar N)).prod (matCircularLaw N r)

/-- The auxiliary law is a probability measure. -/
instance isProbabilityMeasure_auxLaw : IsProbabilityMeasure (auxLaw N r) := by
  unfold auxLaw
  infer_instance

/-- The propagator `𝓜(ω, s, u, ((t, θ), G)) = P_θ'⁻¹ K P_θ'`, `K = rawKernel … s u ω t`. -/
def refM (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (ω : FlowSample N) (s u : ℝ)
    (x : AuxSample N r) : Matrix (Fin N) (Fin N) ℂ :=
  phK (rawKernel F a c b₀ ℓ s u ω x.1.1) x.1.2

/-- The noise `Ξ(ω, s, u, ((t, θ), G)) = P_θ'⁻¹ √(1 - KKᴴ) G`, `K = rawKernel … s u ω t`. -/
def refXi (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (ω : FlowSample N) (s u : ℝ)
    (x : AuxSample N r) : Fin N → Fin r → ℂ :=
  arrayMul (phL (rawKernel F a c b₀ ℓ s u ω x.1.1) x.1.2) x.2

/-- The coordinate maps of `FlowSample N × Ω_aux` used below are measurable. -/
theorem measurable_aux_coords {Ω : Type*} [MeasurableSpace Ω] :
    Measurable (fun p : Ω × AuxSample N r => (p.1, p.2.1.1)) ∧
      Measurable (fun p : Ω × AuxSample N r => p.2.1.2) ∧
      Measurable (fun p : Ω × AuxSample N r => p.2.2) := by
  have h1 : Measurable (fun p : Ω × AuxSample N r => p.2) := measurable_snd
  have h2 : Measurable (fun q : AuxSample N r => q.1) := measurable_fst
  have h3 : Measurable (fun q : unitInterval × Torus N => q.1) := measurable_fst
  have h4 : Measurable (fun q : unitInterval × Torus N => q.2) := measurable_snd
  have h5 : Measurable (fun q : AuxSample N r => q.2) := measurable_snd
  exact ⟨measurable_fst.prodMk (h3.comp (h2.comp h1)), h4.comp (h2.comp h1), h5.comp h1⟩

/-- **Joint measurability of `𝓜`**, for every `s, u`. -/
theorem measurable_refM_joint (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (s u : ℝ) :
    Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (AuxSample N r))]
      (fun p : FlowSample N × AuxSample N r => refM F a c b₀ ℓ p.1 s u p.2) := by
  let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
  obtain ⟨h1, h2, -⟩ := measurable_aux_coords (N := N) (r := r) (Ω := FlowSample N)
  have hR : Measurable fun q : FlowSample N × unitInterval => rawKernel F a c b₀ ℓ s u q.1 q.2 :=
    measurable_rawKernel F a c b₀ ℓ s u
  have hK : Measurable fun p : FlowSample N × AuxSample N r =>
      rawKernel F a c b₀ ℓ s u p.1 p.2.1.1 := hR.comp h1
  have h := measurable_phK.comp (hK.prodMk h2)
  exact h

/-- **Joint measurability of `Ξ`**, for every `s, u`. -/
theorem measurable_refXi_joint (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (s u : ℝ) :
    Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (AuxSample N r))]
      (fun p : FlowSample N × AuxSample N r => refXi F a c b₀ ℓ p.1 s u p.2) := by
  let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
  obtain ⟨h1, h2, h3⟩ := measurable_aux_coords (N := N) (r := r) (Ω := FlowSample N)
  have hR : Measurable fun q : FlowSample N × unitInterval => rawKernel F a c b₀ ℓ s u q.1 q.2 :=
    measurable_rawKernel F a c b₀ ℓ s u
  have hK : Measurable fun p : FlowSample N × AuxSample N r =>
      rawKernel F a c b₀ ℓ s u p.1 p.2.1.1 := hR.comp h1
  have hL : Measurable fun p : FlowSample N × AuxSample N r =>
      phL (rawKernel F a c b₀ ℓ s u p.1 p.2.1.1) p.2.1.2 := by
    have h := measurable_phL.comp (hK.prodMk h2)
    exact h
  have h := continuous_arrayMul_joint.measurable.comp (hL.prodMk h3)
  exact h

/-- For each path, `𝓜 s u` is measurable on `Ω_aux`. -/
theorem measurable_refM (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (ω : FlowSample N)
    (s u : ℝ) : Measurable (refM (r := r) F a c b₀ ℓ ω s u) := by
  have h1 : Measurable fun x : AuxSample N r => x.1.1 :=
    (measurable_fst : Measurable fun q : unitInterval × Torus N => q.1).comp measurable_fst
  have h2 : Measurable fun x : AuxSample N r => x.1.2 :=
    (measurable_snd : Measurable fun q : unitInterval × Torus N => q.2).comp measurable_fst
  have hK : Measurable fun x : AuxSample N r => rawKernel F a c b₀ ℓ s u ω x.1.1 :=
    (measurable_rawKernel_left F a c b₀ ℓ s u ω).comp h1
  have h := measurable_phK.comp (hK.prodMk h2)
  exact h

/-- For each path, `Ξ s u` is measurable on `Ω_aux`. -/
theorem measurable_refXi (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (ω : FlowSample N)
    (s u : ℝ) : Measurable (refXi (r := r) F a c b₀ ℓ ω s u) := by
  have h1 : Measurable fun x : AuxSample N r => x.1.1 :=
    (measurable_fst : Measurable fun q : unitInterval × Torus N => q.1).comp measurable_fst
  have h2 : Measurable fun x : AuxSample N r => x.1.2 :=
    (measurable_snd : Measurable fun q : unitInterval × Torus N => q.2).comp measurable_fst
  have h3 : Measurable fun x : AuxSample N r => x.2 := measurable_snd
  have hK : Measurable fun x : AuxSample N r => rawKernel F a c b₀ ℓ s u ω x.1.1 :=
    (measurable_rawKernel_left F a c b₀ ℓ s u ω).comp h1
  have hL := measurable_phL.comp (hK.prodMk h2)
  have h := continuous_arrayMul_joint.measurable.comp (hL.prodMk h3)
  exact h

/-!
## The per-path reference flow for `canonFlow`
-/

/-- A positive damping floor: `b₀N/ℓ` if `N > 0` (vacuous if `N = 0`). -/
theorem exists_refDamping_floor (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) {b₀ : ℝ} (hb₀ : 0 < b₀)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (ω : FlowSample N) :
    ∃ b : ℝ, 0 < b ∧ ∀ x ∈ Icc a c, ∀ k, b ≤ refDamping F a b₀ ω ℓ x k := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨1, one_pos, fun _ _ k => k.elim0⟩
  · have h1 : (0 : ℝ) < N := by exact_mod_cast hN
    have h2 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    exact ⟨b₀ * N / ℓ, by positivity, fun _ _ _ => le_max_right _ _⟩

section Canon

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobeniusBorelSpace

/-- **The per-path reference flow** (`Palm.ReferenceFlow`) for the kernel of
`canonFlow a c (shortRate) (refDamping)` on the driver space of `dirac ()`, for every path
`ω ∈ simpleRatSet F a c`, with no hypothesis beyond the path's. -/
theorem isReferenceFlow_canon {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    (hac : a < c) {b₀ : ℝ} (hb₀ : 0 < b₀) {ℓ : ℕ} (hℓ : 0 < ℓ) {ω : FlowSample N}
    (hω : ω ∈ RelativeDuhamel.simpleRatSet F a c) :
    BlockBand.Palm.ReferenceFlow.IsReferenceFlow (Measure.dirac ()) (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c
      (refKernel c (canonFlow a c (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ)))
      (refFactor c (canonFlow a c (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ))) := by
  have hadm := admissible_of_mem hF hac.le le_rfl hω b₀ ℓ
  have h𝓝 := canonFlow_isRotationFlow hac.le hadm
  obtain ⟨b, hb0, hfloor⟩ := exists_refDamping_floor F a c hb₀ hℓ ω
  have hcon := kernelContracts_of (ItoNative.itoProductRuleFor_holds _) hac.le hadm.1 hadm.2.1
    hadm.2.2.1 hadm.2.2.2.1 h𝓝
  have hback := backwardEquation_holds (fun S _ μ _ => ItoNative.itoFormulaFor_holds μ)
    BlockBand.GaussianCalculus.gaussianIdentitiesMultivariate_holds.1 hac.le hb0 hadm.1 hadm.2.1
    hadm.2.2.1 hadm.2.2.2.1 hadm.2.2.2.2 hfloor h𝓝 hcon
  exact isReferenceFlow_of
    (BlockBand.SourceProcess.Stochastic.RotationFlow.linearRotationFlowContract_holds N) hac.le
    hb0 hadm.1 hadm.2.1 hadm.2.2.1 hadm.2.2.2.1 hadm.2.2.2.2 hfloor h𝓝 hcon hback

end Canon

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
