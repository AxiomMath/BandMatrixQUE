module

public import BlockBand.Critical.RelativeVectors.PhaseAvg
public import BlockBand.Critical.RelativeVectors.TimeBound
public import BlockBand.Critical.RelativeVectors.StochasticStatements

/-!
# The phase-averaged backward function of a reference flow

* `backward_phase_invariant`: if `(P_α^{-1}𝓜P_α, P_α^{-1}Ξ)` has the law of `(𝓜, Ξ)` for
  every label phase (`IsReferenceFlow.phase_covariant`) and `f` is label-phase invariant
  (`phaseCLM` form), then `g(u z) = g(z)` for all unit `u`; this is the hypothesis `hinv` of
  `crossError_backward_le`, `generatorDiff_backward_le` and `genDiff_rowTail_le`.
* `rows_reference`: the rows of `𝓜_{s,c}` have Euclidean norm `≤ 1` (contraction field).
* `contDiff_backward`: `g_s` is `C²` (from `IsReferenceFlow.backward` applied to the
  `IsArrayC2Bounded 1` test `arrayTest ι f`).
* `hinv_reference`: `backward_phase_invariant` for the reference flow and `arrayTest ι f`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N r k : ℕ}

theorem phase_conj_identity (α : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℂ)
    (X z : Fin N → Fin r → ℂ) :
    phaseCLM (fun i => Complex.exp ((α i : ℂ) * Complex.I))
        (arrayMul (labelPhaseMatrix α M) z + labelPhase (fun i => -α i) X) =
      arrayMul M (phaseCLM (fun i => Complex.exp ((α i : ℂ) * Complex.I)) z) + X := by
  funext i q
  simp only [phaseCLM_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, arrayMul,
    labelPhaseMatrix, labelPhase, Matrix.of_apply]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have h : Complex.exp ((α i : ℂ) * Complex.I) * Complex.exp (-((α i : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_add]; simp
    calc Complex.exp ((α i : ℂ) * Complex.I) *
          (Complex.exp (-((α i : ℂ) * Complex.I)) * M i j * Complex.exp ((α j : ℂ) * Complex.I) *
            z j q)
        = (Complex.exp ((α i : ℂ) * Complex.I) * Complex.exp (-((α i : ℂ) * Complex.I))) *
            (M i j * (Complex.exp ((α j : ℂ) * Complex.I) * z j q)) := by ring
      _ = _ := by rw [h, one_mul]
  · have h : Complex.exp ((α i : ℂ) * Complex.I) * Complex.exp (((-α i : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]; push_cast; simp
    rw [← mul_assoc, h, one_mul]

theorem unit_eq_exp {u : ℂ} (hu : ‖u‖ = 1) : u = Complex.exp ((Complex.arg u : ℂ) * Complex.I) := by
  have h := Complex.norm_mul_exp_arg_mul_I u
  rw [hu, Complex.ofReal_one, one_mul] at h
  exact h.symm

/-- **The backward function of a label-phase-invariant test is label-phase invariant.** -/
theorem backward_phase_invariant {Ωa : Type*} [MeasurableSpace Ωa] {Pa : Measure Ωa}
    {A : Ωa → Matrix (Fin N) (Fin N) ℂ} {X : Ωa → Fin N → Fin r → ℂ} (hA : Measurable A)
    (hX : Measurable X)
    (hcov : ∀ α : Fin N → ℝ,
      Pa.map (fun ω' => (labelPhaseMatrix α (A ω'), labelPhase (fun i => -α i) (X ω'))) =
        Pa.map (fun ω' => (A ω', X ω')))
    {f : (Fin N → Fin r → ℂ) → ℝ} (hf : Continuous f)
    (hinv : ∀ u : Fin N → ℂ, (∀ i, ‖u i‖ = 1) → ∀ z, f (phaseCLM u z) = f z)
    (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ = 1) (z : Fin N → Fin r → ℂ) :
    ∫ ω', f (arrayMul (A ω') (phaseCLM u z) + X ω') ∂Pa =
      ∫ ω', f (arrayMul (A ω') z + X ω') ∂Pa := by
  set α : Fin N → ℝ := fun i => Complex.arg (u i) with hα
  have hu' : u = fun i => Complex.exp ((α i : ℂ) * Complex.I) := funext fun i => unit_eq_exp (hu i)
  set e : Fin N → ℂ := fun i => Complex.exp ((α i : ℂ) * Complex.I) with he
  have heu : ∀ i, ‖e i‖ = 1 := fun i => Complex.norm_exp_ofReal_mul_I _
  set G : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) → ℝ :=
    fun p => f (phaseCLM e (arrayMul p.1 z + p.2)) with hG
  have hGc : Continuous G := by
    refine hf.comp ((phaseCLM e).continuous.comp ?_)
    exact ((continuous_arrayMul_apply z).comp continuous_fst).add continuous_snd
  have hm1 : Measurable fun ω' => (labelPhaseMatrix α (A ω'), labelPhase (fun i => -α i) (X ω')) := by
    have hc1 : Continuous fun M : Matrix (Fin N) (Fin N) ℂ => labelPhaseMatrix α M := by
      unfold labelPhaseMatrix
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.of_apply]
      exact (continuous_const.mul (continuous_id.matrix_elem i j)).mul continuous_const
    have hc2 : Continuous fun Y : Fin N → Fin r → ℂ => labelPhase (fun i => -α i) Y := by
      unfold labelPhase
      refine continuous_pi fun i => ?_
      exact (continuous_apply i).const_smul (Complex.exp (((-α i : ℝ) : ℂ) * Complex.I))
    exact (hc1.measurable.comp hA).prodMk (hc2.measurable.comp hX)
  have hm2 : Measurable fun ω' => (A ω', X ω') := hA.prodMk hX
  have h1 := integral_map hm1.aemeasurable hGc.aestronglyMeasurable (μ := Pa)
  have h2 := integral_map hm2.aemeasurable hGc.aestronglyMeasurable (μ := Pa)
  rw [hcov α] at h1
  rw [h1] at h2
  have l : ∀ ω', G (labelPhaseMatrix α (A ω'), labelPhase (fun i => -α i) (X ω')) =
      f (arrayMul (A ω') (phaseCLM u z) + X ω') := by
    intro ω'
    simp only [hG]
    rw [he, phase_conj_identity, ← he, hu']
  have rr : ∀ ω', G (A ω', X ω') = f (arrayMul (A ω') z + X ω') := by
    intro ω'
    simp only [hG]
    exact hinv e heu _
  simp only [l, rr] at h2
  exact h2

section Reference

variable {F : Matrix (Fin N) (Fin N) ℂ} {a c b₀ : ℝ} {ℓ : ℕ} {ω : FlowSample N}
  {Ωaux : Type} [MeasurableSpace Ωaux] {Paux : Measure Ωaux}
  {𝓜 : ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ} {Ξ : ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ}

/-- The rows of `𝓜_{s,u}` have Euclidean norm `≤ 1`. -/
theorem rows_reference (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ) (hb₀ : 0 ≤ b₀)
    {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (huc : u ≤ c) (ω' : Ωaux) (i : Fin N) :
    ∑ j, ‖𝓜 s u ω' i j‖ ^ 2 ≤ 1 := by
  refine row_sq_le_of_contraction (fun v => ?_) i
  refine (hR.contraction s u has hsu huc ω' v).trans ?_
  have h0 : 0 ≤ b₀ * N * (u - s) / (2 * ℓ) := by
    have : 0 ≤ u - s := by linarith
    positivity
  have : Real.exp (-(b₀ * N * (u - s) / (2 * ℓ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hl := Real.sqrt_nonneg (∑ k, ‖v k‖ ^ 2)
  unfold l2Norm
  nlinarith

/-- **`IsC2Bounded` gives `TestedSetting` for the reference flow.** -/
theorem testedSetting_reference [IsProbabilityMeasure Paux]
    (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ) (hb₀ : 0 ≤ b₀) {s : ℝ} (hs : s ∈ Icc a c)
    (ι : Fin k → Fin N) {f : MarkArray k r → ℝ} (hf : IsC2Bounded 1 f) :
    TestedSetting Paux (𝓜 s c) (Ξ s c) (phaseAvg N ι f) 1 1 1 := by
  have hp := isC2Bounded_phaseAvg (N := N) ι hf
  exact
    { measM := (hR.measurable s c).1
      measXi := (hR.measurable s c).2
      entry := fun ω' i j => entry_le_of_row
        (rows_reference hR hb₀ hs.1 hs.2 le_rfl ω') i j
      c2 := hp.contDiff
      bound0 := hp.bound
      bound1 := hp.deriv_bound
      bound2 := fun y => hp.norm_fderiv_fderiv_le y
      nonneg1 := zero_le_one
      nonneg2 := zero_le_one }

/-- The backward function of `arrayTest ι f` is `IsArrayC2Bounded 1`. -/
theorem isArrayC2Bounded_backward (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ)
    {s : ℝ} (hs : s ∈ Icc a c) (ι : Fin k → Fin N) {f : MarkArray k r → ℝ}
    (hf : IsC2Bounded 1 f) :
    IsArrayC2Bounded 1 (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 s c ω') z + Ξ s c ω') ∂Paux) :=
  (hR.backward 1 (arrayTest ι f) (isArrayC2Bounded_arrayTest ι hf)).1 s hs

/-- **The backward function is `C²`**, in the form of `generatorDiff_backward_le`. -/
theorem contDiff_backward (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ)
    {s : ℝ} (hs : s ∈ Icc a c) (ι : Fin k → Fin N) {f : MarkArray k r → ℝ}
    (hf : IsC2Bounded 1 f) :
    ContDiff ℝ 2 (fun z => ∫ ω', phaseAvg N ι f (testProj ι (arrayMul (𝓜 s c ω') z +
      Ξ s c ω')) ∂Paux) :=
  (isArrayC2Bounded_backward hR hs ι hf).contDiff

/-- `hinv` of `generatorDiff_backward_le` for the reference flow and the phase-averaged test. -/
theorem hinv_reference (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ)
    {s : ℝ} (hs : s ∈ Icc a c) (ι : Fin k → Fin N) {f : MarkArray k r → ℝ}
    (hf : IsC2Bounded 1 f) (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ = 1) (z : Fin N → Fin r → ℂ) :
    (∫ ω', phaseAvg N ι f (testProj ι (arrayMul (𝓜 s c ω') (phaseCLM u z) + Ξ s c ω')) ∂Paux) =
      ∫ ω', phaseAvg N ι f (testProj ι (arrayMul (𝓜 s c ω') z + Ξ s c ω')) ∂Paux :=
  backward_phase_invariant (f := arrayTest ι f) (hR.measurable s c).1 (hR.measurable s c).2
    (hR.phase_covariant s c hs.1 hs.2 le_rfl)
    (isArrayC2Bounded_arrayTest ι hf).contDiff.continuous
    (fun u hu z => arrayTest_phaseCLM ι u hu z) u hu z

end Reference

end BlockBand.Critical.RelativeVectors
