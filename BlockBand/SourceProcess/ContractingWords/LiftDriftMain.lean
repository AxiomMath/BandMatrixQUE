module

public import BlockBand.SourceProcess.ContractingWords.LiftDrift
public import BlockBand.SourceProcess.ContractingWords.EarlyPins
public import BlockBand.SourceProcess.ContractingWords.IncrementHolds

/-!
# The lifted drift majorant

The majorant `driftMaj = C₁ Σ_Z e_j|1_A Z_j| + C₁ layerRem(e_j)` of the drift error along the
path, its nonnegativity, and the fact that it dominates the one-layer bound on the survival event.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.Bridge
open scoped ENNReal

variable {W nT nI : ℕ}

/-- The lifted majorant `C₁ Σ_Z e_j|1_A Z_j| + C₁ layerRem(e_j)`. -/
def driftMaj (b E : ℝ) (s : ℂ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (W j d : ℕ)
    (C₁ : ℝ) (L : List (List (TraceWord nT nI))) (ω : GrowthPath W) : ℝ :=
  C₁ * (L.map fun Zs => pathErr b E s W j ω *
      ‖(alive b E k q K ε W j).indicator (fun ω => productValue b E k q W j ω Zs) ω‖).sum +
    C₁ * ((W : ℝ)⁻¹ / Real.sqrt W + pathErr b E s W j ω ^ 2 + pathErr b E s W j ω ^ (2 * d + 4))

theorem driftMaj_nonneg (b E : ℝ) (s : ℂ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ)
    (W j d : ℕ) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (L : List (List (TraceWord nT nI))) (ω : GrowthPath W) :
    0 ≤ driftMaj b E s k q K ε W j d C₁ L ω := by
  have he := pathErr_nonneg b E s W j ω
  have hs : 0 ≤ (L.map fun Zs => pathErr b E s W j ω *
      ‖(alive b E k q K ε W j).indicator (fun ω => productValue b E k q W j ω Zs) ω‖).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨Zs, -, rfl⟩ := List.mem_map.mp hx; positivity
  unfold driftMaj; positivity

/-- On the survival event, the one-layer bound in path form. -/
theorem driftMaj_ge {b E : ℝ} {s : ℂ} {k : Fin nT → ℕ} {q : Fin nI → ℝ → ℝ} {K ε : ℝ} {j d : ℕ}
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (L : List (List (TraceWord nT nI))) {ω : GrowthPath W}
    (hA : ω ∈ alive b E k q K ε W j)
    (h : ∀ Zs : List (TraceWord nT nI),
      productValue b E k q W j ω Zs = coreProd (letterMatrix b E k q W j ω)
        (sepOf b E (pathXX E W j ω)) Zs) {x : ℝ}
    (hx : x ≤ C₁ * layerErr b E s (pathXX E W j ω) * (L.map fun Zs =>
        ‖coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) Zs‖).sum +
      C₁ * layerRem W d (layerErr b E s (pathXX E W j ω))) :
    x ≤ driftMaj b E s k q K ε W j d C₁ L ω := by
  have hab := abs_layerErr_le_pathErr b E s j ω
  have hS : 0 ≤ (L.map fun Zs =>
      ‖coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) Zs‖).sum :=
    List.sum_nonneg fun y hy => by obtain ⟨Zs, -, rfl⟩ := List.mem_map.mp hy; positivity
  have hsum : (L.map fun Zs =>
      ‖coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) Zs‖).sum *
        pathErr b E s W j ω = (L.map fun Zs => pathErr b E s W j ω *
      ‖(alive b E k q K ε W j).indicator (fun ω => productValue b E k q W j ω Zs) ω‖).sum := by
    rw [← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun Zs _ => ?_
    rw [Set.indicator_of_mem hA, h Zs, mul_comm]
  refine hx.trans ?_
  unfold driftMaj
  rw [← hsum]
  have h1 : layerErr b E s (pathXX E W j ω) ≤ pathErr b E s W j ω := (le_abs_self _).trans hab
  have h2 := layerRem_mono W d hab
  have h3 : C₁ * layerErr b E s (pathXX E W j ω) * (L.map fun Zs =>
      ‖coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) Zs‖).sum ≤
      C₁ * ((L.map fun Zs =>
      ‖coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) Zs‖).sum *
        pathErr b E s W j ω) := by
    rw [mul_assoc, mul_comm (layerErr _ _ _ _)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hS) hC₁
  have h4 : C₁ * layerRem W d (layerErr b E s (pathXX E W j ω)) ≤
      C₁ * ((W : ℝ)⁻¹ / Real.sqrt W + pathErr b E s W j ω ^ 2 +
        pathErr b E s W j ω ^ (2 * d + 4)) := mul_le_mul_of_nonneg_left h2 hC₁
  linarith

end BlockBand.SourceProcess.ContractingWords
