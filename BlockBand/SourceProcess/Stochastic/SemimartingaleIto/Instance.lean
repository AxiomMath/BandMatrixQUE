module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.PathFacts
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The augmented Taylor-scheme instance for the Itô formula)

Data: the contract's `Y, β, α` on `(Ω, 𝓖)`, `φ`, a random time `σ` (later a stopping time with
`σ ≤ T`), an open `W` (the starting window: `σ = 0` off `{Y_0 ∈ W}`) and a point `y⋆`.
With `st = stopTime σ`, `dr_u = itoDrift φ (Y_u) u β_u α_u` (`driftPath`):

* `augA t = 1_{Y_0∈W} φ(0, Y_0) + ∫_0^t 1_{v ≤ σ} dr_v dv`;
* `augZ t = (st t, augA t, Y_{st t})` on `{Y_0 ∈ W}`, `(st t, augA t, y⋆)` off it;
* `augβ = (1_{u≤σ}, 1_{u≤σ} dr_u, 1_{u≤σ} β_u)`, `augα = embA (1_{u≤σ} α_u)`;
* `augN = (0, 0, MN)`, `augB = (0, 0; 0, MB)` for given martingales `MN`, `MB`.

Pathwise identities: `integral_switch_path` (`∫_0^t 1_{v≤σ} f = ∫_0^{t∧σ} f`), the coordinate
compensators `drI_augβ_*`, and `ctrl_aug` (`ctrl(augβ, augα) = 1_{u≤σ}(1 + |dr_u| + ctrl(β,α))`).
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {Ω : Type*} {d : ℕ}

/-- `α` as a function-valued process (to feed the scheme). -/
def matF (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) : ℝ≥0 → Ω → Fin d → Fin d → ℝ :=
  fun u ω i j => α u ω i j

/-- `dr_u = itoDrift φ (Y_u) u β_u α_u`. -/
def driftPath (φ : ℝ × (Fin d → ℝ) → ℝ) (Y β : ℝ≥0 → Ω → Fin d → ℝ)
    (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) : ℝ≥0 → Ω → ℝ :=
  fun u ω => itoDrift φ (Y u ω) u (β u ω) (α u ω)

/-- `br_u = itoBracket φ (Y_u) u α_u`. -/
def bracketPath (φ : ℝ × (Fin d → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) : ℝ≥0 → Ω → ℝ :=
  fun u ω => itoBracket φ (Y u ω) u (α u ω)

variable (φ : ℝ × (Fin d → ℝ) → ℝ) (Y β : ℝ≥0 → Ω → Fin d → ℝ)
  (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (σ : Ω → WithTop ℝ≥0) (W : Set (Fin d → ℝ))
  (ys : Fin d → ℝ)

open Classical in
/-- The compensator coordinate. -/
def augA (t : ℝ≥0) (ω : Ω) : ℝ :=
  (if Y 0 ω ∈ W then φ (0, Y 0 ω) else 0) +
    ∫ v in Ioc (0 : ℝ) t, switchAfter σ (driftPath φ Y β α) v.toNNReal ω

open Classical in
/-- The augmented state. -/
def augZ (t : ℝ≥0) (ω : Ω) : Fin (d + 2) → ℝ :=
  consAug (stopTime (σ ω) t : ℝ) (augA φ Y β α σ W t ω)
    (if Y 0 ω ∈ W then Y (stopTime (σ ω) t) ω else ys)

/-- The augmented drift. -/
def augβ (u : ℝ≥0) (ω : Ω) : Fin (d + 2) → ℝ :=
  consAug (switchAfter σ (fun _ _ => (1 : ℝ)) u ω) (switchAfter σ (driftPath φ Y β α) u ω)
    (switchAfter σ β u ω)

/-- The augmented covariance. -/
def augα (u : ℝ≥0) (ω : Ω) : Fin (d + 2) → Fin (d + 2) → ℝ := embA (matF (switchAfter σ α) u ω)

/-- The augmented martingales. -/
def augN (MN : Fin d → ℝ≥0 → Ω → ℝ) : Fin (d + 2) → ℝ≥0 → Ω → ℝ :=
  Fin.cons (0 : ℝ≥0 → Ω → ℝ) (Fin.cons (0 : ℝ≥0 → Ω → ℝ) MN)

/-- The augmented bracket martingales. -/
def augB (MB : Fin d → Fin d → ℝ≥0 → Ω → ℝ) : Fin (d + 2) → Fin (d + 2) → ℝ≥0 → Ω → ℝ :=
  Fin.cons (0 : Fin (d + 2) → ℝ≥0 → Ω → ℝ) (Fin.cons (0 : Fin (d + 2) → ℝ≥0 → Ω → ℝ)
    fun i => Fin.cons (0 : ℝ≥0 → Ω → ℝ) (Fin.cons (0 : ℝ≥0 → Ω → ℝ) (MB i)))

variable {φ Y β α σ W ys}

theorem stopTime_zero' (τ : WithTop ℝ≥0) : stopTime τ 0 = 0 :=
  le_antisymm (stopTime_le τ 0) zero_le

theorem stopTime_eq_of_le {τ : WithTop ℝ≥0} {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) ≤ τ) :
    stopTime τ u = u :=
  le_antisymm (stopTime_le τ u) (le_stopTime hu le_rfl)

theorem stopTime_le_of_le {τ : WithTop ℝ≥0} {T : ℝ≥0} (hτ : τ ≤ T) (t : ℝ≥0) :
    stopTime τ t ≤ T :=
  WithTop.coe_le_coe.1 ((stopTime_le_self τ t).trans hτ)

theorem stopTime_of_eq_zero' (t : ℝ≥0) : stopTime 0 t = 0 :=
  le_antisymm (WithTop.coe_le_coe.1 (stopTime_le_self 0 t)) zero_le

/-- `∫_0^t 1_{v ≤ σ} f_v = ∫_0^{t∧σ} f_v`. -/
theorem integral_switch_path {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ℝ≥0 → Ω → G) (t : ℝ≥0) (ω : Ω) :
    ∫ v in Ioc (0 : ℝ) t, switchAfter σ f v.toNNReal ω =
      ∫ v in Ioc (0 : ℝ) (stopTime (σ ω) t), f v.toNNReal ω := by
  rw [← setIntegral_switch (fun v : ℝ => f v.toNNReal ω) (σ ω) t]
  rfl

theorem switchAfter_apply {G : Type*} [Zero G] (f : ℝ≥0 → Ω → G) (u : ℝ≥0) (ω : Ω) :
    switchAfter σ f u ω = if (u : WithTop ℝ≥0) ≤ σ ω then f u ω else 0 := rfl

theorem switchAfter_of_le {G : Type*} [Zero G] {f : ℝ≥0 → Ω → G} {u : ℝ≥0} {ω : Ω}
    (h : (u : WithTop ℝ≥0) ≤ σ ω) : switchAfter σ f u ω = f u ω := by
  unfold switchAfter; split_ifs; rfl

theorem switchAfter_of_not_le {G : Type*} [Zero G] {f : ℝ≥0 → Ω → G} {u : ℝ≥0} {ω : Ω}
    (h : ¬ (u : WithTop ℝ≥0) ≤ σ ω) : switchAfter σ f u ω = 0 := by
  unfold switchAfter; split_ifs; rfl

theorem abs_switchAfter (f : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) :
    |switchAfter σ f u ω| = switchAfter σ (fun u ω => |f u ω|) u ω := by
  simp only [switchAfter_apply]; split_ifs <;> simp

theorem ctrl_aug (u : ℝ≥0) (ω : Ω) :
    ctrl (augβ φ Y β α σ) (augα α σ) u ω =
      switchAfter σ (fun u ω => 1 + |driftPath φ Y β α u ω| + ctrl β (matF α) u ω) u ω := by
  unfold ctrl augβ augα
  rw [sum_aug, sum_aug]
  simp only [consAug_zero, consAug_one, consAug_ss, embA_zero, embA_one, embA_ss,
    abs_zero, Finset.sum_const_zero, zero_add]
  simp only [sum_aug, consAug_zero, consAug_one, consAug_ss, abs_zero, zero_add]
  by_cases h : (u : WithTop ℝ≥0) ≤ σ ω
  · simp only [switchAfter_of_le h, abs_one, matF]; ring
  · simp [switchAfter_of_not_le h, matF]

theorem augZ_zero_coord (t : ℝ≥0) (ω : Ω) :
    augZ φ Y β α σ W ys t ω 0 = stopTime (σ ω) t := rfl

theorem augZ_one_coord (t : ℝ≥0) (ω : Ω) :
    augZ φ Y β α σ W ys t ω (Fin.succ 0) = augA φ Y β α σ W t ω := rfl

open Classical in
theorem augZ_ss_coord (t : ℝ≥0) (ω : Ω) (i : Fin d) :
    augZ φ Y β α σ W ys t ω i.succ.succ =
      (if Y 0 ω ∈ W then Y (stopTime (σ ω) t) ω else ys) i := rfl

theorem augA_zero (ω : Ω) [Decidable (Y 0 ω ∈ W)] :
    augA φ Y β α σ W 0 ω = if Y 0 ω ∈ W then φ (0, Y 0 ω) else 0 := by
  simp only [augA, NNReal.coe_zero, Ioc_self, Measure.restrict_empty, integral_zero_measure,
    add_zero]
  congr 1

theorem drI_augβ_zero (t : ℝ≥0) (ω : Ω) :
    drI (augβ φ Y β α σ) 0 t ω = stopTime (σ ω) t := by
  unfold drI augβ
  simp only [consAug_zero]
  rw [integral_switch_path (fun _ _ => (1 : ℝ)) t ω]
  simp [Measure.real, Real.volume_Ioc]

theorem drI_augβ_one (t : ℝ≥0) (ω : Ω) :
    drI (augβ φ Y β α σ) (Fin.succ 0) t ω =
      ∫ v in Ioc (0 : ℝ) t, switchAfter σ (driftPath φ Y β α) v.toNNReal ω := rfl

theorem drI_augβ_ss (t : ℝ≥0) (ω : Ω) (i : Fin d) :
    drI (augβ φ Y β α σ) i.succ.succ t ω =
      ∫ v in Ioc (0 : ℝ) (stopTime (σ ω) t), β v.toNNReal ω i := by
  unfold drI augβ
  simp only [consAug_ss]
  rw [← integral_switch_path (σ := σ) (fun u ω => β u ω i) t ω]
  congr 1; funext v
  simp only [switchAfter_apply]; split_ifs <;> rfl

theorem difJ_augα_ss (t : ℝ≥0) (ω : Ω) (i j : Fin d) :
    difJ (augα α σ) i.succ.succ j.succ.succ t ω =
      ∫ v in Ioc (0 : ℝ) (stopTime (σ ω) t), α v.toNNReal ω i j := by
  unfold difJ augα
  simp only [embA_ss, consAug_ss]
  rw [← integral_switch_path (σ := σ) (fun u ω => α u ω i j) t ω]
  congr 1; funext v
  by_cases h : ((v.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ σ ω
  · simp only [matF, switchAfter_of_le h]
  · simp only [matF, switchAfter_of_not_le h]; rfl

theorem augα_zero_row (u : ℝ≥0) (ω : Ω) (l : Fin (d + 2)) : augα α σ u ω 0 l = 0 := rfl

theorem augα_one_row (u : ℝ≥0) (ω : Ω) (l : Fin (d + 2)) :
    augα α σ u ω (Fin.succ 0) l = 0 := rfl

theorem augα_ss_zero (u : ℝ≥0) (ω : Ω) (i : Fin d) : augα α σ u ω i.succ.succ 0 = 0 := rfl

theorem augα_ss_one (u : ℝ≥0) (ω : Ω) (i : Fin d) :
    augα α σ u ω i.succ.succ (Fin.succ 0) = 0 := rfl

theorem difJ_eq_zero_of {α' : ℝ≥0 → Ω → Fin (d + 2) → Fin (d + 2) → ℝ} {k l : Fin (d + 2)}
    (h : ∀ u ω, α' u ω k l = 0) (t : ℝ≥0) (ω : Ω) : difJ α' k l t ω = 0 := by
  simp [difJ, h]

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
