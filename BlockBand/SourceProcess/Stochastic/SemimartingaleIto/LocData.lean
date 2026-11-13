module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Prog
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Localization data and pathwise bounds)

`LocData Q 𝓖 Y β α U W φ σ T c ys` packages: the contract semimartingale `Y` (characteristics
`β, α`) with values a.s. in the open `U`; `φ` Borel and `C²` on `univ ×ˢ U`; an open window `W`
with compact closure in `U`; `ys ∈ U`; a stopping time `σ ≤ T` vanishing off `{Y_0 ∈ W}`, such
that a.s. the stopped path stays in `closure W` (when `Y_0 ∈ W`) and the control
`∫_0^{t∧σ} (Σ|β^i| + Σ|α^{ij}|) ≤ c`.

On the full-measure set `LGood`: `|itoDrift| ≤ M(1 + ctrl)` before `σ` (`LGood.abs_dr_le`),
`|∫_0^{t∧σ} itoDrift| ≤ M (T + c)` (`LGood.abs_int_dr_le`) and
`∫_0^{t∧σ} (1 + |itoDrift| + ctrl) ≤ (1 + M)(T + c)` (`LGood.int_aug_le`), where `M` bounds the
partial derivatives of `φ` on `[0, T] × closure W` (`LocData.bound`).
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}

/-- Hypotheses of the localized Itô step (module docstring). -/
structure LocData (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 m₀) (Y β : ℝ≥0 → Ω → Fin d → ℝ)
    (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (U W : Set (Fin d → ℝ))
    (φ : ℝ × (Fin d → ℝ) → ℝ) (σ : Ω → WithTop ℝ≥0) (T : ℝ≥0) (c : ℝ) (ys : Fin d → ℝ) :
    Prop where
  sm : IsContinuousSemimartingale Q 𝓖 Y β α
  hU : IsOpen U
  hYU : ∀ᵐ ω ∂Q, ∀ t, Y t ω ∈ U
  hφm : Measurable φ
  hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U)
  hW : IsOpen W
  hWc : IsCompact (closure W)
  hWU : closure W ⊆ U
  hys : ys ∈ U
  stop : IsStoppingTime 𝓖 σ
  le_T : ∀ ω, σ ω ≤ T
  off : ∀ ω, Y 0 ω ∉ W → σ ω = 0
  exit : ∀ᵐ ω ∂Q, Y 0 ω ∈ W → ∀ t, Y (stopTime (σ ω) t) ω ∈ closure W
  level : ∀ᵐ ω ∂Q, ∀ t, ctrlI β (matF α) (stopTime (σ ω) t) ω ≤ c

/-- The pathwise good set. -/
def LGood (Y β : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (U W : Set (Fin d → ℝ)) (σ : Ω → WithTop ℝ≥0) (c : ℝ) (ω : Ω) : Prop :=
  Continuous (fun t => Y t ω) ∧ (∀ t, Y t ω ∈ U) ∧
  (∀ t : ℝ≥0, (∀ i, IntegrableOn (fun s : ℝ => β s.toNNReal ω i) (Ioc 0 t)) ∧
    ∀ i j, IntegrableOn (fun s : ℝ => α s.toNNReal ω i j) (Ioc 0 t)) ∧
  (Y 0 ω ∈ W → ∀ t, Y (stopTime (σ ω) t) ω ∈ closure W) ∧
  (∀ t, ctrlI β (matF α) (stopTime (σ ω) t) ω ≤ c)

variable {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 m₀}
  {Y β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
  {U W : Set (Fin d → ℝ)} {φ : ℝ × (Fin d → ℝ) → ℝ} {σ : Ω → WithTop ℝ≥0} {T : ℝ≥0} {c : ℝ}
  {ys : Fin d → ℝ}

theorem LocData.ae_good (D : LocData Q 𝓖 Y β α U W φ σ T c ys) :
    ∀ᵐ ω ∂Q, LGood Y β α U W σ c ω := by
  filter_upwards [D.sm.continuous, D.hYU, D.sm.integrable, D.exit, D.level] with ω a b e f g
  exact ⟨a, b, e, f, g⟩

/-- One bound for the partial derivatives on `[0, T] × closure W`. -/
theorem LocData.bound (D : LocData Q 𝓖 Y β α U W φ σ T c ys) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ Icc (0 : ℝ) T ×ˢ closure W, |partialTime φ p| ≤ M ∧
      (∀ i, |partialSpace φ p i| ≤ M) ∧ ∀ i j, |partialSpace2 φ p i j| ≤ M :=
  exists_partial_bound D.hU D.hφ (isCompact_Icc.prod D.hWc)
    fun _ hp => ⟨mem_univ _, D.hWU hp.2⟩

theorem integral_Ioc_one (u : ℝ≥0) : ∫ _v in Ioc (0 : ℝ) u, (1 : ℝ) = u := by
  simp [Measure.real, Real.volume_Ioc]

theorem toNNReal_le_stopTime {τ : WithTop ℝ≥0} {t : ℝ≥0} {v : ℝ}
    (hv : v ∈ Ioc (0 : ℝ) (stopTime τ t)) : (v.toNNReal : WithTop ℝ≥0) ≤ τ := by
  refine le_trans (WithTop.coe_le_coe.2 ?_) (stopTime_le_self τ t)
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hv.1.le]; exact hv.2

section Good

variable {ω : Ω} (hω : LGood Y β α U W σ c ω)
include hω

theorem LGood.c_nonneg : 0 ≤ c :=
  (ctrlI_nonneg (β := β) (α := matF α) _ ω).trans (hω.2.2.2.2 0)

theorem LGood.integrableOn_ctrl (u : ℝ≥0) :
    IntegrableOn (fun v : ℝ => ctrl β (matF α) v.toNNReal ω) (Ioc 0 u) := by
  unfold ctrl matF
  exact Integrable.add (integrable_finsetSum _ fun i _ => ((hω.2.2.1 u).1 i).abs)
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ((hω.2.2.1 u).2 i j).abs)

theorem LGood.integrableOn_dr (D : LocData Q 𝓖 Y β α U W φ σ T c ys) (t : ℝ≥0) :
    IntegrableOn (fun s : ℝ => driftPath φ Y β α s.toNNReal ω) (Ioc 0 t) :=
  integrableOn_itoDrift_path D.hU D.hφ hω.1 hω.2.1 t (hω.2.2.1 t).1 (hω.2.2.1 t).2

theorem LGood.mem_closure_of_le (hG : Y 0 ω ∈ W) {v : ℝ≥0} (hv : (v : WithTop ℝ≥0) ≤ σ ω) :
    Y v ω ∈ closure W := by
  have := hω.2.2.2.1 hG v
  rwa [stopTime_eq_of_le hv] at this

theorem LGood.abs_dr_le (D : LocData Q 𝓖 Y β α U W φ σ T c ys) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ p ∈ Icc (0 : ℝ) T ×ˢ closure W, |partialTime φ p| ≤ M ∧
      (∀ i, |partialSpace φ p i| ≤ M) ∧ ∀ i j, |partialSpace2 φ p i j| ≤ M)
    (hG : Y 0 ω ∈ W) {v : ℝ≥0} (hv : (v : WithTop ℝ≥0) ≤ σ ω) :
    |driftPath φ Y β α v ω| ≤ M * (1 + ctrl β (matF α) v ω) := by
  have hvT : (v : ℝ) ≤ T := by exact_mod_cast WithTop.coe_le_coe.1 (hv.trans (D.le_T ω))
  exact abs_itoDrift_le hM0 (hM _ ⟨⟨NNReal.coe_nonneg v, hvT⟩, hω.mem_closure_of_le hG hv⟩)

/-- `∫_0^{t∧σ} (1 + |dr| + ctrl) ≤ (1 + M)(T + c)`. -/
theorem LGood.int_aug_le (D : LocData Q 𝓖 Y β α U W φ σ T c ys) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ p ∈ Icc (0 : ℝ) T ×ˢ closure W, |partialTime φ p| ≤ M ∧
      (∀ i, |partialSpace φ p i| ≤ M) ∧ ∀ i j, |partialSpace2 φ p i j| ≤ M) (t : ℝ≥0) :
    ∫ v in Ioc (0 : ℝ) (stopTime (σ ω) t), (1 + |driftPath φ Y β α v.toNNReal ω| +
      ctrl β (matF α) v.toNNReal ω) ≤ (1 + M) * (T + c) := by
  have hc := hω.c_nonneg
  by_cases hG : Y 0 ω ∈ W
  · have hi := hω.integrableOn_ctrl (stopTime (σ ω) t)
    have hb : ∫ v in Ioc (0 : ℝ) (stopTime (σ ω) t), (1 + M) * (1 + ctrl β (matF α)
        v.toNNReal ω) = (1 + M) * ((stopTime (σ ω) t : ℝ) +
          ctrlI β (matF α) (stopTime (σ ω) t) ω) := by
      rw [integral_const_mul, integral_add (integrable_const _) hi, integral_Ioc_one]; rfl
    have hf : IntegrableOn (fun v : ℝ => 1 + |driftPath φ Y β α v.toNNReal ω| +
        ctrl β (matF α) v.toNNReal ω) (Ioc 0 (stopTime (σ ω) t)) :=
      ((integrable_const (1 : ℝ)).add (hω.integrableOn_dr D _).abs).add hi
    have hg : IntegrableOn (fun v : ℝ => (1 + M) * (1 + ctrl β (matF α) v.toNNReal ω))
        (Ioc 0 (stopTime (σ ω) t)) := ((integrable_const (1 : ℝ)).add hi).const_mul _
    refine (setIntegral_mono_on hf hg measurableSet_Ioc fun v hv => ?_).trans ?_
    · have := hω.abs_dr_le D hM0 hM hG (toNNReal_le_stopTime hv)
      have h0 := ctrl_nonneg (β := β) (α := matF α) v.toNNReal ω
      nlinarith
    · rw [hb]
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ (hω.2.2.2.2 t)) (by positivity)
      exact_mod_cast stopTime_le_of_le (D.le_T ω) t
  · rw [D.off ω hG, stopTime_of_eq_zero']
    simp only [NNReal.coe_zero, Ioc_self, Measure.restrict_empty, integral_zero_measure]
    positivity

/-- `|∫_0^{t∧σ} dr| ≤ M (T + c)`. -/
theorem LGood.abs_int_dr_le (D : LocData Q 𝓖 Y β α U W φ σ T c ys) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ p ∈ Icc (0 : ℝ) T ×ˢ closure W, |partialTime φ p| ≤ M ∧
      (∀ i, |partialSpace φ p i| ≤ M) ∧ ∀ i j, |partialSpace2 φ p i j| ≤ M) (t : ℝ≥0) :
    |∫ v in Ioc (0 : ℝ) (stopTime (σ ω) t), driftPath φ Y β α v.toNNReal ω| ≤ M * (T + c) := by
  have hc := hω.c_nonneg
  by_cases hG : Y 0 ω ∈ W
  · have hi := hω.integrableOn_ctrl (stopTime (σ ω) t)
    rw [← Real.norm_eq_abs]
    have hg : IntegrableOn (fun v : ℝ => M * (1 + ctrl β (matF α) v.toNNReal ω))
        (Ioc 0 (stopTime (σ ω) t)) := ((integrable_const (1 : ℝ)).add hi).const_mul _
    refine (norm_integral_le_of_norm_le hg
      ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun v hv => ?_))).trans ?_
    · rw [Real.norm_eq_abs]; exact hω.abs_dr_le D hM0 hM hG (toNNReal_le_stopTime hv)
    · rw [integral_const_mul, integral_add (integrable_const _) hi, integral_Ioc_one]
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ (hω.2.2.2.2 t)) hM0
      exact_mod_cast stopTime_le_of_le (D.le_T ω) t
  · rw [D.off ω hG, stopTime_of_eq_zero']
    simp only [NNReal.coe_zero, Ioc_self, Measure.restrict_empty, integral_zero_measure,
      abs_zero]
    positivity

end Good

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
