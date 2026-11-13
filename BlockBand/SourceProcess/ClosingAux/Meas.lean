module

public import BlockBand.SourceProcess.ClosingAux.CfcMeas
public import BlockBand.SourceProcess.Sampling.Fubini

/-!
# The closed physical process is measurable: closing data and closing map

Every closing datum is a Borel function of the path sample `ω`:
`farReflection`, `farTransmission`, `omittedProj = cfc 1_{t≤h²} T_far`,
`closingPairing = cfc g T_far · S_ffᴴ` and `farEmbed` (for every real `h`; the cfc of the
discontinuous cutoffs is handled by `measurable_cfc_of_tendsto`). The closing map
`C(z) = (1 - A) + (1 - zN)⁻¹ zT` is jointly measurable in `(S, A, Π, z)` (Lean's totalized
`⁻¹` is `det⁻¹ • adjugate`), hence `physClosingMap … ω (phase θ)` is jointly measurable in
`(ω, θ)` (`measurable_physClosingMap`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingAux

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Closing
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.FullSourceStops

variable {W : ℕ}

theorem measurable_matrix_cmul {α m n : Type*} [MeasurableSpace α] {c : α → ℂ}
    {f : α → Matrix m n ℂ} (hc : Measurable c) (hf : Measurable f) :
    Measurable fun a => c a • f a :=
  Measurable.of_eval_matrix _ fun _ _ => hc.mul hf.eval_matrix

theorem measurable_matrix_add {α m n : Type*} [MeasurableSpace α] {f g : α → Matrix m n ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a + g a :=
  Measurable.of_eval_matrix _ fun _ _ => hf.eval_matrix.add hg.eval_matrix

theorem measurable_farReflection (b E : ℝ) (n : ℕ) : Measurable (farReflection b E W n) :=
  Measurable.of_eval_matrix _ fun _ _ => (measurable_scatteringMatrix b E n).eval_matrix

theorem measurable_farTransmission (b E : ℝ) (n : ℕ) : Measurable (farTransmission b E W n) :=
  have hR := measurable_farReflection (W := W) b E n
  measurable_matrix_sub measurable_const
    (measurable_matrix_mul' (measurable_matrix_conjTranspose' hR) hR)

theorem measurable_omittedProj (b E h : ℝ) (n : ℕ) : Measurable (omittedProj b E h W n) :=
  (measurable_cfc_omitIndicator h).comp (measurable_farTransmission b E n)

theorem measurable_closingPairing (b E h : ℝ) (n : ℕ) :
    Measurable (closingPairing b E h W n) :=
  measurable_matrix_mul' ((measurable_cfc_pairWeight h).comp (measurable_farTransmission b E n))
    (measurable_matrix_conjTranspose' (measurable_farReflection b E n))

theorem measurable_farEmbed {α : Type*} [MeasurableSpace α] {f : α → Matrix (Fin W) (Fin W) ℂ}
    (hf : Measurable f) : Measurable fun a => farEmbed (f a) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [farEmbed, of_apply]
  split_ifs
  · exact hf.eval_matrix
  · exact measurable_const

theorem measurable_closingMap {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
    {S A P : α → Matrix ι ι ℂ} {z : α → ℂ} (hS : Measurable S) (hA : Measurable A)
    (hP : Measurable P) (hz : Measurable z) :
    Measurable fun a => closingMap (S a) (A a) (P a) (z a) := by
  have hN : Measurable fun a => closingN (S a) (A a) (P a) :=
    measurable_matrix_mul' (measurable_matrix_mul' hP hS) hA
  have hT : Measurable fun a => closingT (S a) (A a) (P a) :=
    measurable_matrix_mul' (measurable_matrix_mul' hP hS)
      (measurable_matrix_sub measurable_const hA)
  exact measurable_matrix_add (measurable_matrix_sub measurable_const hA)
    (measurable_matrix_mul' (measurable_matrix_inv.comp
      (measurable_matrix_sub measurable_const (measurable_matrix_cmul hz hN)))
      (measurable_matrix_cmul hz hT))

theorem measurable_phase : Measurable phase := by
  unfold phase; fun_prop

/-- The physical closing map along measurable maps to the path and the phase. -/
theorem measurable_physClosingMap_comp {α : Type*} [MeasurableSpace α] (b E s T h : ℝ)
    {f : α → GrowthPath W} {θ : α → ℝ} (hf : Measurable f) (hθ : Measurable θ) :
    Measurable fun a => physClosingMap b E s T h W (f a) (phase (θ a)) :=
  measurable_closingMap ((measurable_scatteringMatrix b E _).comp hf)
    (measurable_farEmbed ((measurable_omittedProj b E h _).comp hf))
    (measurable_farEmbed ((measurable_closingPairing b E h _).comp hf))
    (measurable_phase.comp hθ)

/-- **The physical closing map is jointly measurable in the path and the phase.** -/
theorem measurable_physClosingMap (b E s T h : ℝ) :
    Measurable fun x : GrowthPath W × ℝ => physClosingMap b E s T h W x.1 (phase x.2) :=
  measurable_physClosingMap_comp b E s T h measurable_fst measurable_snd

end BlockBand.SourceProcess.ClosingAux
