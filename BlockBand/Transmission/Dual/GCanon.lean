module

public import BlockBand.Transmission.Dual.GR4Kernel

/-!
# The canonical sequence space and almost-sure transfer to the conditional kernel

* `CSeq d = ℕ → CPath d` (standard Borel), the truncation `ctrunc t`
  (`ŵ_n ↦ ŵ_n(· ∧ t)`) and the canonical filtration `cfilt d t = comap (ctrunc t)`; it is of the
  form required by `ae_martingale_condKernel` (`cfilt_eq`).
* `ae_ae_condKernel`: an a.s. measurable property of `(ξ, Φ)` holds, for `law ξ`-a.e. `z`,
  `condKernel z`-a.s. at `(z, ·)` (used for the start `Z₀ = z` and for the path properties
  under the kernel).
* `ae_of_ae_condKernel`: the converse, used to integrate the kernel statement
  (`P(Z ∈ A) = ∫ κ(z, A) μ(dz)`) in the random-start form.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {d : ℕ}

/-- The canonical sequence space. -/
abbrev CSeq (d : ℕ) : Type := ℕ → CPath d

/-- Truncation of every path of a sequence at time `t`. -/
def ctrunc (t : ℝ≥0) (ŵ : CSeq d) : CSeq d := fun n =>
  ⟨fun r => (ŵ n).1 (min r t), (ŵ n).2.comp (continuous_id.min continuous_const)⟩

theorem measurable_ctrunc (t : ℝ≥0) : Measurable (ctrunc (d := d) t) := by
  refine measurable_pi_iff.2 fun n => ?_
  have h : Measurable fun ŵ : CSeq d => ŵ n := measurable_pi_apply n
  exact Measurable.subtype_mk (measurable_pi_iff.2 fun r => (measurable_cev (min r t)).comp h)

theorem ctrunc_ctrunc {s t : ℝ≥0} (hst : s ≤ t) (ŵ : CSeq d) :
    ctrunc s (ctrunc t ŵ) = ctrunc s ŵ := by
  funext n; refine Subtype.ext (funext fun r => ?_)
  show (ŵ n).1 (min (min r s) t) = (ŵ n).1 (min r s)
  rw [min_eq_left ((min_le_right r s).trans hst)]

/-- The canonical filtration of the sequence space. -/
def cfilt (d : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (CSeq d)) where
  seq t := MeasurableSpace.comap (ctrunc t) inferInstance
  mono' s t hst := by
    have e : ctrunc (d := d) s = ctrunc s ∘ ctrunc t := funext fun ŵ => (ctrunc_ctrunc hst ŵ).symm
    show MeasurableSpace.comap (ctrunc s) _ ≤ MeasurableSpace.comap (ctrunc t) _
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_ctrunc s).comap_le
  le' t := (measurable_ctrunc t).comap_le

theorem cfilt_eq (t : ℝ≥0) :
    cfilt d t = MeasurableSpace.comap (ctrunc t) inferInstance := rfl

/-- A function of the truncated sequence is `cfilt`-measurable. -/
theorem measurable_cfilt_of_eq {β : Type*} [MeasurableSpace β] {t : ℝ≥0} {f : CSeq d → β}
    (hf : Measurable f) (he : ∀ ŵ, f (ctrunc t ŵ) = f ŵ) : Measurable[cfilt d t] f := by
  have : f = f ∘ ctrunc t := funext fun ŵ => (he ŵ).symm
  rw [this]
  exact hf.comp (comap_measurable (ctrunc t))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E Ω₂ : Type*} [MeasurableSpace E] [MeasurableSpace Ω₂] [StandardBorelSpace Ω₂] [Nonempty Ω₂]
  {ξ : Ω → E} {Φ : Ω → Ω₂}

/-- **An a.s. measurable property passes to the conditional kernel.** -/
theorem ae_ae_condKernel (hξΦ : Measurable fun x => (ξ x, Φ x)) {S : Set (E × Ω₂)}
    (hS : MeasurableSet S) (h : ∀ᵐ x ∂P, (ξ x, Φ x) ∈ S) :
    ∀ᵐ z ∂(jlaw P ξ Φ).fst, ∀ᵐ w ∂(jlaw P ξ Φ).condKernel z, (z, w) ∈ S := by
  refine (Measure.ae_compProd_iff (p := fun p => p ∈ S) hS).1 ?_
  rw [Measure.disintegrate, jlaw, ae_map_iff (p := fun p => p ∈ S) hξΦ.aemeasurable hS]
  exact h

/-- **The converse: integrating a kernel statement.** -/
theorem ae_of_ae_condKernel (hξΦ : Measurable fun x => (ξ x, Φ x)) {S : Set (E × Ω₂)}
    (hS : MeasurableSet S)
    (h : ∀ᵐ z ∂(jlaw P ξ Φ).fst, ∀ᵐ w ∂(jlaw P ξ Φ).condKernel z, (z, w) ∈ S) :
    ∀ᵐ x ∂P, (ξ x, Φ x) ∈ S := by
  have h' := (Measure.ae_compProd_iff (p := fun p => p ∈ S) hS).2 h
  rw [Measure.disintegrate, jlaw, ae_map_iff (p := fun p => p ∈ S) hξΦ.aemeasurable hS] at h'
  exact h'

omit [IsProbabilityMeasure P] [StandardBorelSpace Ω₂] [Nonempty Ω₂] in
/-- The law of the start is the first marginal of the joint law. -/
theorem jlaw_fst (hξ : Measurable ξ) (hΦ : Measurable Φ) :
    (jlaw P ξ Φ).fst = P.map ξ := by
  rw [jlaw, Measure.fst, Measure.map_map measurable_fst (hξ.prodMk hΦ)]
  rfl

omit [IsProbabilityMeasure P] in
/-- **A martingale cut off by a time-0 event is a martingale** (used for the start cut-off that
makes the canonical martingale-problem functionals bounded). -/
theorem Martingale.indicator_zero {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration P 𝓖] {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 P) {G : Set Ω}
    (hG : MeasurableSet[𝓖 0] G) : Martingale (fun t => G.indicator (M t)) 𝓖 P := by
  refine ⟨fun t => (hM.1 t).indicator (𝓖.mono zero_le G hG), fun s t hst => ?_⟩
  filter_upwards [condExp_indicator (m := 𝓖 s) (hM.integrable t) (𝓖.mono zero_le G hG),
    hM.condExp_ae_eq hst] with x h1 h2
  rw [h1]
  by_cases hx : x ∈ G
  · simp only [indicator_of_mem hx, h2]
  · simp only [indicator_of_notMem hx]

end BlockBand.Transmission.Dual.G
