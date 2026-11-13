module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Instance
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Progressive measurability of the Itô coefficients)

Raw filtration `𝓖`. For strongly progressive `Y, β, α` and Borel measurable `φ` (no regularity:
the partial derivatives are measurable by `measurable_fderiv`):

* `isStronglyProgressive_driftPath`, `isStronglyProgressive_bracketPath`,
  `isStronglyProgressive_ctrl`: `u ↦ itoDrift φ (Y_u) u β_u α_u`, `u ↦ itoBracket φ (Y_u) u α_u`
  and `Σ|β^i| + Σ|α^{ij}|` are strongly progressive;
* `isStronglyProgressive_phi`: `u ↦ φ(u, Y_u)` is strongly progressive;
* `stronglyMeasurable_consAug`, `continuous_consAug_comp`: the block vector of measurable
  (continuous) components is measurable (continuous).
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {d : ℕ}

theorem continuous_consAug : Continuous fun q : (ℝ × ℝ) × (Fin d → ℝ) =>
    consAug q.1.1 q.1.2 q.2 := by
  refine continuous_pi fun k => ?_
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k
  · exact continuous_fst.comp continuous_fst
  · exact continuous_snd.comp continuous_fst
  · exact (continuous_apply i).comp continuous_snd

theorem continuous_consAug_comp {X : Type*} [TopologicalSpace X] {a b : X → ℝ}
    {c : X → Fin d → ℝ} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous fun x => consAug (a x) (b x) (c x) :=
  continuous_consAug.comp ((ha.prodMk hb).prodMk hc)

theorem stronglyMeasurable_consAug {X : Type*} {m : MeasurableSpace X} {a b : X → ℝ}
    {c : X → Fin d → ℝ} (ha : StronglyMeasurable a) (hb : StronglyMeasurable b)
    (hc : StronglyMeasurable c) : StronglyMeasurable fun x => consAug (a x) (b x) (c x) :=
  continuous_consAug.comp_stronglyMeasurable ((ha.prodMk hb).prodMk hc)

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m₀}
  {Y β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}

theorem measurable_time_coord (i : ℝ≥0) :
    Measurable[Subtype.instMeasurableSpace.prod (𝓖 i)] fun p : Set.Iic i × Ω => (p.1 : ℝ≥0) :=
  measurable_subtype_coe.comp measurable_fst

theorem measurable_matF_prog (hα : IsStronglyProgressive 𝓖 α) (i : ℝ≥0) :
    Measurable[Subtype.instMeasurableSpace.prod (𝓖 i)]
      fun p : Set.Iic i × Ω => matF α p.1 p.2 := by
  refine @Measurable.of_eval _ _ _ (Subtype.instMeasurableSpace.prod (𝓖 i)) _ _ fun k => ?_
  refine @Measurable.of_eval _ _ _ (Subtype.instMeasurableSpace.prod (𝓖 i)) _ _ fun l => ?_
  exact ((continuous_id.matrix_elem k l).comp_stronglyMeasurable (hα i)).measurable

theorem isStronglyProgressive_driftPath (φ : ℝ × (Fin d → ℝ) → ℝ)
    (hY : IsStronglyProgressive 𝓖 Y) (hβ : IsStronglyProgressive 𝓖 β)
    (hα : IsStronglyProgressive 𝓖 α) : IsStronglyProgressive 𝓖 (driftPath φ Y β α) := by
  intro i
  exact (@measurable_itoDrift_comp d _ (Subtype.instMeasurableSpace.prod (𝓖 i)) φ _ _ _ _
    (measurable_time_coord i) (hY i).measurable (hβ i).measurable
    (measurable_matF_prog hα i)).stronglyMeasurable

theorem isStronglyProgressive_bracketPath (φ : ℝ × (Fin d → ℝ) → ℝ)
    (hY : IsStronglyProgressive 𝓖 Y) (hα : IsStronglyProgressive 𝓖 α) :
    IsStronglyProgressive 𝓖 (bracketPath φ Y α) := by
  intro i
  exact (@measurable_itoBracket_comp d _ (Subtype.instMeasurableSpace.prod (𝓖 i)) φ _ _ _
    (measurable_time_coord i) (hY i).measurable (measurable_matF_prog hα i)).stronglyMeasurable

theorem isStronglyProgressive_ctrl (hβ : IsStronglyProgressive 𝓖 β)
    (hα : IsStronglyProgressive 𝓖 α) : IsStronglyProgressive 𝓖 (ctrl β (matF α)) := by
  intro i
  unfold ctrl matF
  refine (Finset.stronglyMeasurable_fun_sum _ fun k _ => ?_).add
    (Finset.stronglyMeasurable_fun_sum _ fun k _ => Finset.stronglyMeasurable_fun_sum _
      fun l _ => ?_)
  · exact (continuous_abs.comp (continuous_apply k)).comp_stronglyMeasurable (hβ i)
  · exact (continuous_abs.comp (continuous_id.matrix_elem k l)).comp_stronglyMeasurable (hα i)

theorem isStronglyProgressive_phi {φ : ℝ × (Fin d → ℝ) → ℝ} (hφ : Measurable φ)
    (hY : IsStronglyProgressive 𝓖 Y) :
    IsStronglyProgressive 𝓖 fun u ω => φ ((u : ℝ), Y u ω) := by
  intro i
  exact (hφ.comp ((measurable_coe_nnreal_real.comp (measurable_time_coord i)).prodMk
    (hY i).measurable)).stronglyMeasurable

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
