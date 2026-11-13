module

public import BlockBand.Critical.RelativeVectors.DuhamelInterface

/-!
# The backward function of a reference flow

For an auxiliary probability space `(Ωaux, Paux)`, propagators `𝓜, Ξ` and a path-dependent test
`h` as in `RelativeDuhamelStatement`, the backward function is
`backwardFn Paux 𝓜 Ξ c h ω s z = ∫ h ω (𝓜^ω_{s,c} z + Ξ^ω_{s,c}) dPaux`; it is the `g` of
`RelativeDuhamelStatement` by definition (`backwardFn_eq`).

* `backwardFn_terminal`: `g_c = h` for a reference flow (`𝓜_{c,c} = 1`, `Ξ_{c,c} = 0`).
* `backwardFn_phaseInvariant`: label-phase invariance of `g_s`, `s ∈ [a, c]`, from
  `phase_covariant` and the invariance of `h ω` (`arrayMul_labelPhase`).
* `measurable_backwardFn`: `ω ↦ g ω s z` is `pathSigma F a a c`-measurable (parametric integral
  for the product σ-algebra `pathSigma ⊗ Borel(Ωaux)`).
* `measurable_fderiv_apply`, `measurable_fderiv_fderiv_apply`: for any family of functions that
  is pointwise measurable in the parameter and differentiable (resp. `C²`) for every parameter,
  the directional first and second derivatives are measurable in the parameter (limits of
  difference quotients). `measurable_switch_derivs` applies this to the switched family
  `ω ↦ if π ω ∈ S then g (π ω) s else h (π ω)` used in the limit argument (with `π = hermProj`,
  or `id`).
* `arrayC2_norm_fderiv_le`, `arrayC2_norm_fderiv_fderiv_le`, `arrayC2_abs_le`: Euclidean
  bounded-`C²` gives sup-norm operator bounds with the factor `K = √(N r)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel

open MeasureTheory Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Critical.RelativeVectors
open BlockBand.Palm.MomentFlow

variable {N r : ℕ}

/-!
## The backward function
-/

/-- Backward function `g^ω_s(z) = E_aux h_ω(𝓜^ω_{s,c} z + Ξ^ω_{s,c})`. -/
def backwardFn {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ) (c : ℝ)
    (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ) (ω : FlowSample N) (s : ℝ)
    (z : Fin N → Fin r → ℂ) : ℝ :=
  ∫ ω', h ω (arrayMul (𝓜 ω s c ω') z + Ξ ω s c ω') ∂Paux

/-- `backwardFn` is the interface's `g` (the `let` of `RelativeDuhamelStatement`). -/
theorem backwardFn_eq {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ) (c : ℝ)
    (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ) :
    backwardFn Paux 𝓜 Ξ c h =
      fun ω s z => ∫ ω', h ω (arrayMul (𝓜 ω s c ω') z + Ξ ω s c ω') ∂Paux := rfl

/-- `1 z = z`. -/
theorem arrayMul_one (z : Fin N → Fin r → ℂ) : arrayMul (1 : Matrix (Fin N) (Fin N) ℂ) z = z := by
  funext i q
  simp [arrayMul, Matrix.one_apply]

/-- **Terminal value.** For a reference flow, `g_c = h`. -/
theorem backwardFn_terminal {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    [IsProbabilityMeasure Paux]
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ)
    {F : Matrix (Fin N) (Fin N) ℂ} {a c b₀ : ℝ} {ℓ : ℕ}
    (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ) (ω : FlowSample N)
    (hRF : IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω)) (z : Fin N → Fin r → ℂ) :
    backwardFn Paux 𝓜 Ξ c h ω c z = h ω z := by
  have e : ∀ ω', h ω (arrayMul (𝓜 ω c c ω') z + Ξ ω c c ω') = h ω z := fun ω' => by
    rw [(hRF.initial c ω').1, (hRF.initial c ω').2, arrayMul_one, add_zero]
  simp only [backwardFn, e, integral_const, probReal_univ, one_smul]

/-!
## Label phases
-/

/-- `M (P_α z) = P_α ((P_α^{-1} M P_α) z)`. -/
theorem arrayMul_labelPhase (α : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℂ)
    (z : Fin N → Fin r → ℂ) :
    arrayMul M (labelPhase α z) = labelPhase α (arrayMul (labelPhaseMatrix α M) z) := by
  funext i q
  simp only [arrayMul, labelPhase, labelPhaseMatrix, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Complex.exp ((α i : ℂ) * Complex.I) * Complex.exp (-((α i : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc M i j * (Complex.exp ((α j : ℂ) * Complex.I) * z j q)
      = (Complex.exp ((α i : ℂ) * Complex.I) * Complex.exp (-((α i : ℂ) * Complex.I))) *
          (M i j * (Complex.exp ((α j : ℂ) * Complex.I) * z j q)) := by rw [e, one_mul]
    _ = _ := by ring

/-- Label phases are additive. -/
theorem labelPhase_add (α : Fin N → ℝ) (x y : Fin N → Fin r → ℂ) :
    labelPhase α (x + y) = labelPhase α x + labelPhase α y := by
  funext i
  simp [labelPhase, smul_add]

/-- `P_α P_{-α} = 1`. -/
theorem labelPhase_neg_cancel (α : Fin N → ℝ) (x : Fin N → Fin r → ℂ) :
    labelPhase α (labelPhase (fun i => -α i) x) = x := by
  funext i
  simp only [labelPhase, smul_smul, ← Complex.exp_add]
  have : (α i : ℂ) * Complex.I + ((-α i : ℝ) : ℂ) * Complex.I = 0 := by push_cast; ring
  rw [this, Complex.exp_zero, one_smul]

/-- Continuity of `M ↦ M z`. -/
theorem continuous_arrayMul_left (z : Fin N → Fin r → ℂ) :
    Continuous fun M : Matrix (Fin N) (Fin N) ℂ => arrayMul M z := by
  refine continuous_pi fun i => continuous_pi fun q => ?_
  simp only [arrayMul]
  exact continuous_finsetSum _ fun j _ => (continuous_apply_apply i j).mul continuous_const

/-- Continuity of the phase conjugation `M ↦ P_α^{-1} M P_α`. -/
theorem continuous_labelPhaseMatrix (α : Fin N → ℝ) :
    Continuous fun M : Matrix (Fin N) (Fin N) ℂ => labelPhaseMatrix α M := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [labelPhaseMatrix, Matrix.of_apply]
  exact (continuous_const.mul (continuous_apply_apply i j)).mul continuous_const

/-- Continuity of the label phases `z ↦ P_α z`. -/
theorem continuous_labelPhase (α : Fin N → ℝ) :
    Continuous fun z : Fin N → Fin r → ℂ => labelPhase α z := by
  refine continuous_pi fun i => ?_
  simp only [labelPhase]
  fun_prop

/-- **Phase invariance of the backward function.** For a reference flow and a measurable
label-phase-invariant `h ω`, every `g_s`, `s ∈ [a, c]`, is label-phase invariant (no bound on
`h ω` is needed). -/
theorem backwardFn_phaseInvariant {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ)
    {F : Matrix (Fin N) (Fin N) ℂ} {a c b₀ : ℝ} {ℓ : ℕ}
    (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ) (ω : FlowSample N)
    (hRF : IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω))
    (hinv : IsLabelPhaseInvariant (h ω)) (hmeas : Measurable (h ω)) {s : ℝ} (hs : s ∈ Icc a c) :
    IsLabelPhaseInvariant (backwardFn Paux 𝓜 Ξ c h ω s) := by
  intro α z
  show ∫ ω', h ω (arrayMul (𝓜 ω s c ω') (labelPhase α z) + Ξ ω s c ω') ∂Paux =
    ∫ ω', h ω (arrayMul (𝓜 ω s c ω') z + Ξ ω s c ω') ∂Paux
  set Φ : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) → ℝ :=
    fun p => h ω (arrayMul p.1 z + p.2) with hΦdef
  have hΦ : Measurable Φ :=
    hmeas.comp (((continuous_arrayMul_left z).measurable.comp measurable_fst).add measurable_snd)
  have hpt : ∀ ω', h ω (arrayMul (𝓜 ω s c ω') (labelPhase α z) + Ξ ω s c ω') =
      Φ (labelPhaseMatrix α (𝓜 ω s c ω'), labelPhase (fun i => -α i) (Ξ ω s c ω')) := by
    intro ω'
    have e : arrayMul (𝓜 ω s c ω') (labelPhase α z) + Ξ ω s c ω' =
        labelPhase α (arrayMul (labelPhaseMatrix α (𝓜 ω s c ω')) z +
          labelPhase (fun i => -α i) (Ξ ω s c ω')) := by
      rw [labelPhase_add, labelPhase_neg_cancel, arrayMul_labelPhase]
    rw [e]
    exact hinv α _
  have hM := hRF.measurable s c
  have hpair' : Measurable fun ω' =>
      (labelPhaseMatrix α (𝓜 ω s c ω'), labelPhase (fun i => -α i) (Ξ ω s c ω')) :=
    ((continuous_labelPhaseMatrix α).measurable.comp hM.1).prodMk
      ((continuous_labelPhase _).measurable.comp hM.2)
  have hpair : Measurable fun ω' => (𝓜 ω s c ω', Ξ ω s c ω') := hM.1.prodMk hM.2
  have hcov := hRF.phase_covariant s c hs.1 hs.2 le_rfl α
  calc ∫ ω', h ω (arrayMul (𝓜 ω s c ω') (labelPhase α z) + Ξ ω s c ω') ∂Paux
      = ∫ ω', Φ (labelPhaseMatrix α (𝓜 ω s c ω'), labelPhase (fun i => -α i) (Ξ ω s c ω'))
          ∂Paux := integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ p, Φ p ∂(Paux.map fun ω' =>
          (labelPhaseMatrix α (𝓜 ω s c ω'), labelPhase (fun i => -α i) (Ξ ω s c ω'))) :=
        (integral_map hpair'.aemeasurable hΦ.aestronglyMeasurable).symm
    _ = ∫ p, Φ p ∂(Paux.map fun ω' => (𝓜 ω s c ω', Ξ ω s c ω')) := by rw [hcov]
    _ = ∫ ω', Φ (𝓜 ω s c ω', Ξ ω s c ω') ∂Paux :=
        integral_map hpair.aemeasurable hΦ.aestronglyMeasurable

/-!
## Measurability in the path
-/

/-- Parametric integrals of functions measurable for `mα ⊗ Borel` are `mα`-measurable. -/
theorem measurable_integral_prod {α β : Type*} {mα : MeasurableSpace α} [MeasurableSpace β]
    (ν : Measure β) [SFinite ν] {f : α × β → ℝ}
    (hf : Measurable[MeasurableSpace.comap Prod.fst mα ⊔
      MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace β)] f) :
    Measurable fun x => ∫ y, f (x, y) ∂ν :=
  (StronglyMeasurable.integral_prod_right' (ν := ν) hf.stronglyMeasurable).measurable

/-- **Measurability in the path.** Under the interface's joint measurability of `𝓜, Ξ` and `h`
for `pathSigma F a a c ⊗ Borel`, `ω ↦ g ω s z` is `pathSigma F a a c`-measurable for all `s, z`
(no bound on `h` is needed). -/
theorem measurable_backwardFn {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    [IsProbabilityMeasure Paux]
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ)
    (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ)
    (hMΞ : ∀ s u,
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => 𝓜 p.1 s u p.2) ∧
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => Ξ p.1 s u p.2))
    (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ)
    (hh : Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin N → Fin r → ℂ))]
      (Function.uncurry h))
    (s : ℝ) (z : Fin N → Fin r → ℂ) :
    Measurable[pathSigma F a a c] fun ω => backwardFn Paux 𝓜 Ξ c h ω s z := by
  let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
  have hw : Measurable fun p : FlowSample N × Ωaux =>
      arrayMul (𝓜 p.1 s c p.2) z + Ξ p.1 s c p.2 :=
    ((continuous_arrayMul_left z).measurable.comp (hMΞ s c).1).add (hMΞ s c).2
  have hf : Measurable fun p : FlowSample N × Ωaux =>
      h p.1 (arrayMul (𝓜 p.1 s c p.2) z + Ξ p.1 s c p.2) :=
    hh.comp (measurable_fst.prodMk hw)
  exact measurable_integral_prod (mα := pathSigma F a a c) Paux hf

/-!
## Measurability of directional derivatives in a parameter
-/

/-- **Directional derivatives are measurable in the parameter.** If `ω ↦ G ω z` is measurable for
every `z` and every `G ω` is differentiable, then `ω ↦ DG_ω(z) v` is measurable (it is the limit
of the difference quotients along `t = 1/(k+1)`). -/
theorem measurable_fderiv_apply {α E : Type*} {m : MeasurableSpace α} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : α → E → ℝ} (hG : ∀ z, Measurable fun ω => G ω z)
    (hd : ∀ ω, Differentiable ℝ (G ω)) (z v : E) :
    Measurable fun ω => fderiv ℝ (G ω) z v := by
  set t : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => by
        simp only [t, mem_compl_iff, mem_singleton_iff]; positivity⟩
  refine measurable_of_tendsto_metrizable
    (f := fun k ω => (t k)⁻¹ • (G ω (z + t k • v) - G ω z)) (fun k => ?_) ?_
  · simp only [smul_eq_mul]
    exact measurable_const.mul ((hG _).sub (hG z))
  · rw [tendsto_pi_nhds]
    intro ω
    exact (((hd ω z).hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero).comp ht

/-- **Second directional derivatives are measurable in the parameter.** If `ω ↦ G ω z` is
measurable for every `z` and every `G ω` is `C²`, then `ω ↦ D²G_ω(z)(v, w)` is measurable. -/
theorem measurable_fderiv_fderiv_apply {α E : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {G : α → E → ℝ}
    (hG : ∀ z, Measurable fun ω => G ω z) (hd : ∀ ω, ContDiff ℝ 2 (G ω)) (z v w : E) :
    Measurable fun ω => fderiv ℝ (fderiv ℝ (G ω)) z v w := by
  have hd1 : ∀ ω, Differentiable ℝ (G ω) := fun ω => (hd ω).differentiable (by norm_num)
  have hd2 : ∀ ω, Differentiable ℝ (fderiv ℝ (G ω)) := fun ω =>
    ((hd ω).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : ∀ y, Measurable fun ω => fderiv ℝ (G ω) y w := fun y =>
    measurable_fderiv_apply hG hd1 y w
  have hd1' : ∀ ω, Differentiable ℝ fun y => fderiv ℝ (G ω) y w := fun ω y =>
    (hd2 ω y).clm_apply (differentiableAt_const w)
  have e : ∀ ω, fderiv ℝ (fun y => fderiv ℝ (G ω) y w) z v =
      fderiv ℝ (fderiv ℝ (G ω)) z v w := by
    intro ω
    rw [fderiv_clm_apply (hd2 ω z) (differentiableAt_const w)]
    simp
  have key := measurable_fderiv_apply h1 hd1' z v
  simp only [e] at key
  exact key

/-- **The switched backward family** `ω ↦ (if π ω ∈ S then g (π ω) s else h (π ω))` for a map `π`
into the flow samples (in the limit argument, `π = hermProj` and `m = comap hermProj pathSigma`;
or `π = id`, `m = pathSigma`). If `π` is `m`-to-`pathSigma` measurable, `S` is
`pathSigma`-measurable, `g (π ω) s` is `C²` whenever `π ω ∈ S`, and `h (π ω)` is `C²` for all `ω`,
then the value, the first and the second directional derivatives at every point are
`m`-measurable in `ω`. -/
theorem measurable_switch_derivs {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    [IsProbabilityMeasure Paux]
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ)
    (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ)
    (hMΞ : ∀ s u,
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => 𝓜 p.1 s u p.2) ∧
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => Ξ p.1 s u p.2))
    (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ)
    (hh : Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin N → Fin r → ℂ))]
      (Function.uncurry h))
    {α : Type*} (m : MeasurableSpace α) (π : α → FlowSample N)
    (hπ : @Measurable α (FlowSample N) m (pathSigma F a a c) π)
    (S : Set (FlowSample N)) [∀ x, Decidable (x ∈ S)] (hS : MeasurableSet[pathSigma F a a c] S)
    (s : ℝ)
    (hgS : ∀ ω, π ω ∈ S → ContDiff ℝ 2 (backwardFn Paux 𝓜 Ξ c h (π ω) s))
    (hhC : ∀ ω, ContDiff ℝ 2 (h (π ω))) :
    let K : α → (Fin N → Fin r → ℂ) → ℝ := fun ω =>
      if π ω ∈ S then backwardFn Paux 𝓜 Ξ c h (π ω) s else h (π ω)
    ∀ z v w : Fin N → Fin r → ℂ,
      Measurable[m] (fun ω => K ω z) ∧ Measurable[m] (fun ω => fderiv ℝ (K ω) z v) ∧
        Measurable[m] (fun ω => fderiv ℝ (fderiv ℝ (K ω)) z v w) := by
  intro K
  have hval : ∀ z, Measurable[m] fun ω => K ω z := by
    intro z
    have hg : Measurable[pathSigma F a a c] fun ω => backwardFn Paux 𝓜 Ξ c h ω s z :=
      measurable_backwardFn Paux 𝓜 Ξ F a c hMΞ h hh s z
    have hh' : Measurable[pathSigma F a a c] fun ω => h ω z := by
      let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
      exact hh.comp (measurable_id.prodMk measurable_const)
    have e : (fun ω => K ω z) = fun ω =>
        if π ω ∈ S then backwardFn Paux 𝓜 Ξ c h (π ω) s z else h (π ω) z := by
      funext ω
      simp only [K]
      split_ifs <;> rfl
    rw [e]
    exact Measurable.ite (hπ hS) (hg.comp hπ) (hh'.comp hπ)
  have hC : ∀ ω, ContDiff ℝ 2 (K ω) := by
    intro ω
    simp only [K]
    split_ifs with hω
    · exact hgS ω hω
    · exact hhC ω
  intro z v w
  exact ⟨hval z, measurable_fderiv_apply hval (fun ω => (hC ω).differentiable (by norm_num)) z v,
    measurable_fderiv_fderiv_apply hval hC z v w⟩

/-- **Item 4, unswitched form.** If every `g ω s` is `C²`, then `ω ↦ Dg(z)v` and `ω ↦ D²g(z)(v,w)`
are `pathSigma F a a c`-measurable. -/
theorem measurable_fderiv_backwardFn {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    [IsProbabilityMeasure Paux]
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ)
    (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ)
    (hMΞ : ∀ s u,
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => 𝓜 p.1 s u p.2) ∧
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => Ξ p.1 s u p.2))
    (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ)
    (hh : Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin N → Fin r → ℂ))]
      (Function.uncurry h))
    (s : ℝ) (hgC : ∀ ω, ContDiff ℝ 2 (backwardFn Paux 𝓜 Ξ c h ω s))
    (z v w : Fin N → Fin r → ℂ) :
    Measurable[pathSigma F a a c] (fun ω => fderiv ℝ (backwardFn Paux 𝓜 Ξ c h ω s) z v) ∧
      Measurable[pathSigma F a a c]
        (fun ω => fderiv ℝ (fderiv ℝ (backwardFn Paux 𝓜 Ξ c h ω s)) z v w) := by
  have hval : ∀ z, Measurable[pathSigma F a a c] fun ω => backwardFn Paux 𝓜 Ξ c h ω s z :=
    fun z => measurable_backwardFn Paux 𝓜 Ξ F a c hMΞ h hh s z
  exact ⟨measurable_fderiv_apply hval (fun ω => (hgC ω).differentiable (by norm_num)) z v,
    measurable_fderiv_fderiv_apply hval hgC z v w⟩

/-!
## Euclidean to sup-norm operator bounds
-/

/-- `‖v‖₂ ≤ √(N r) ‖v‖_∞` on arrays. -/
theorem sqrt_arrayNormSq_le (v : Fin N → Fin r → ℂ) :
    Real.sqrt (arrayNormSq v) ≤ Real.sqrt (N * r) * ‖v‖ := by
  have h1 : arrayNormSq v ≤ ((N : ℝ) * r) * ‖v‖ ^ 2 := by
    unfold arrayNormSq
    calc ∑ i, ∑ q, ‖v i q‖ ^ 2 ≤ ∑ _i : Fin N, ∑ _q : Fin r, ‖v‖ ^ 2 := by
          gcongr with i _ q _
          exact (norm_le_pi_norm (v i) q).trans (norm_le_pi_norm v i)
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  calc Real.sqrt (arrayNormSq v) ≤ Real.sqrt (((N : ℝ) * r) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- The constant of a Euclidean bounded-`C²` function is nonnegative. -/
theorem arrayC2_nonneg {C : ℝ} {g : (Fin N → Fin r → ℂ) → ℝ}
    (hg : IsArrayC2Bounded C g) : 0 ≤ C :=
  (abs_nonneg _).trans (hg.bound 0)

/-- `|g z| ≤ C`. -/
theorem arrayC2_abs_le {C : ℝ} {g : (Fin N → Fin r → ℂ) → ℝ}
    (hg : IsArrayC2Bounded C g) (z : Fin N → Fin r → ℂ) : |g z| ≤ C :=
  hg.bound z

/-- **Sup-norm bound on `Dg`.** `‖Dg(z)‖ ≤ C √(N r)` (operator norm for the sup norm). -/
theorem arrayC2_norm_fderiv_le {C : ℝ} {g : (Fin N → Fin r → ℂ) → ℝ}
    (hg : IsArrayC2Bounded C g) (z : Fin N → Fin r → ℂ) :
    ‖fderiv ℝ g z‖ ≤ C * Real.sqrt (N * r) := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (arrayC2_nonneg hg) (Real.sqrt_nonneg _)) fun v => ?_
  rw [Real.norm_eq_abs]
  calc |fderiv ℝ g z v| ≤ C * Real.sqrt (arrayNormSq v) := hg.deriv_bound z v
    _ ≤ C * (Real.sqrt (N * r) * ‖v‖) :=
        mul_le_mul_of_nonneg_left (sqrt_arrayNormSq_le v) (arrayC2_nonneg hg)
    _ = C * Real.sqrt (N * r) * ‖v‖ := by ring

/-- **Sup-norm bound on `D²g`.** `‖D²g(z)‖ ≤ C √(N r)²` (operator norm for the sup norm). -/
theorem arrayC2_norm_fderiv_fderiv_le {C : ℝ} {g : (Fin N → Fin r → ℂ) → ℝ}
    (hg : IsArrayC2Bounded C g) (z : Fin N → Fin r → ℂ) :
    ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ C * Real.sqrt (N * r) ^ 2 := by
  have hC := (arrayC2_nonneg hg)
  have hK := Real.sqrt_nonneg ((N : ℝ) * r)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [Real.norm_eq_abs]
  calc |fderiv ℝ (fderiv ℝ g) z v w| ≤
        C * Real.sqrt (arrayNormSq v) * Real.sqrt (arrayNormSq w) := hg.hessian_bound z v w
    _ ≤ C * (Real.sqrt (N * r) * ‖v‖) * (Real.sqrt (N * r) * ‖w‖) := by
        gcongr
        · exact sqrt_arrayNormSq_le v
        · exact sqrt_arrayNormSq_le w
    _ = C * Real.sqrt (N * r) ^ 2 * ‖v‖ * ‖w‖ := by ring

end BlockBand.Critical.RelativeVectors.RelativeDuhamel
