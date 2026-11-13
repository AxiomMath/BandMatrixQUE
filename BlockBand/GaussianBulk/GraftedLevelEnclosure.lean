module
public import BlockBand.GaussianBulk.GraftedLevelIntersections

/-!
# Enclosure and saddle geometry of the grafted level loop

Defines the grafted level loop `nativeGraftedLevelLoop` from the source `d` and a saddle `x₀`:
outer endpoints `±(Σ_j |d_j| + √t)`, central interval `[x₀ - r, x₀ + r]` with
`r = η²/(8√tmax)`, and mesh cap `√t/(2N²)`. The loop avoids every real pole `d_j`, meets the
vertical line `Re z = x₀` exactly at the conjugate saddle pair, and contains both saddle points.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set
open scoped BigOperators

/-- The enclosing radius `Σ_j |d_j|` of the source. -/
def graftedDeformationRadius {N : ℕ} (d : Fin N → ℝ) : ℝ := ∑ j, |d j|

/-- Every source point lies in `[-Σ|d_j|, Σ|d_j|]`. -/
theorem graftedDeformationRadius_bounds {N : ℕ} (d : Fin N → ℝ) (j : Fin N) :
    -graftedDeformationRadius d ≤ d j ∧ d j ≤ graftedDeformationRadius d := by
  have hj : |d j| ≤ graftedDeformationRadius d :=
    Finset.single_le_sum (fun k _ => abs_nonneg (d k)) (Finset.mem_univ j)
  exact abs_le.mp hj

/-- The endpoints `±(Σ|d_j| + √t)` strictly enclose every real pole, including repeated poles. -/
theorem graftedDeformationRadius_encloses {N : ℕ} (d : Fin N → ℝ)
    (t : ℝ) (ht : 0 < t) (j : Fin N) :
    -graftedDeformationRadius d-Real.sqrt t < d j ∧
      d j < graftedDeformationRadius d+Real.sqrt t := by
  have hb := graftedDeformationRadius_bounds d j
  have hs := Real.sqrt_pos.mpr ht
  constructor <;> linarith

/-- The central half-width `η²/(8√tmax)`, half the radius of the positive-height neighborhood. -/
def graftedCentralRadius (tmax eta : ℝ) : ℝ := eta^2/(8*Real.sqrt tmax)

/-- The central endpoints `x₀ ± r` lie strictly inside the outer enclosure, and the central
interval lies within `η²/(4√tmax)` of `x₀`. -/
theorem graftedCentralGeometry {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t tmax eta x₀ : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (heta : 0 < eta) (hheight : eta ≤ levelHeight d t x₀) :
    let r := graftedCentralRadius tmax eta;
    -graftedDeformationRadius d-Real.sqrt t < x₀-r ∧
      x₀-r < x₀ ∧ x₀ < x₀+r ∧
      x₀+r < graftedDeformationRadius d+Real.sqrt t ∧
      ∀ x ∈ Icc (x₀-r) (x₀+r), |x-x₀| ≤ eta^2/(4*Real.sqrt tmax) := by
  let r := graftedCentralRadius tmax eta
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hr : 0 < r := by dsimp [r,graftedCentralRadius];positivity
  have he : eta^2/(4*Real.sqrt tmax)=2*r := by dsimp [r,graftedCentralRadius];ring
  have hclose (x : ℝ) (hx : x ∈ Icc (x₀-r) (x₀+r)) :
      |x-x₀| ≤ eta^2/(4*Real.sqrt tmax) := by
    rw [he]
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2]
  have ha : 0 < levelHeight d t (x₀-r) := by
    have hb := levelHeight_neighborhood_lower hN d t tmax eta x₀ (x₀-r)
      ht htmax heta hheight (hclose _ ⟨le_rfl,by linarith⟩)
    linarith
  have hb : 0 < levelHeight d t (x₀+r) := by
    have hb := levelHeight_neighborhood_lower hN d t tmax eta x₀ (x₀+r)
      ht htmax heta hheight (hclose _ ⟨by linarith,le_rfl⟩)
    linarith
  have hsupporta := levelHeight_support_interval hN d t (x₀-r)
    (-graftedDeformationRadius d) (graftedDeformationRadius d) ht
    (graftedDeformationRadius_bounds d) ha
  have hsupportb := levelHeight_support_interval hN d t (x₀+r)
    (-graftedDeformationRadius d) (graftedDeformationRadius d) ht
    (graftedDeformationRadius_bounds d) hb
  exact ⟨hsupporta.1,by linarith,by linarith,hsupportb.2,hclose⟩

/-- The grafted level loop determined by the source `d`, the times `t ≤ tmax`, the height `η`
and the saddle abscissa `x₀`. -/
def nativeGraftedLevelLoop {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t tmax eta x₀ : ℝ) (ht : 0 < t) :=
  actualGraftedLevelLoop hN d t
    (-graftedDeformationRadius d-Real.sqrt t)
    (x₀-graftedCentralRadius tmax eta) (x₀+graftedCentralRadius tmax eta)
    (graftedDeformationRadius d+Real.sqrt t)
    (Real.sqrt t/(2*(N : ℝ)^2)) ht

/-- The grafted level loop avoids every real pole, for `N > 0`, `0 < t ≤ tmax` and
`0 < η ≤ levelHeight d t x₀`. -/
theorem nativeGraftedLevelLoop_ne_pole {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t tmax eta x₀ : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (heta : 0 < eta) (hheight : eta ≤ levelHeight d t x₀) (j : Fin N) :
    ∀ z ∈ range (nativeGraftedLevelLoop hN d t tmax eta x₀ ht), z ≠ (d j : ℂ) := by
  have hg := graftedCentralGeometry hN d t tmax eta x₀ ht htmax heta hheight
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  exact actualGraftedLevelLoop_ne_pole hN d t tmax eta x₀ _ _ _ _ _
    ht htmax heta hheight hg.1 (le_trans hg.2.1.le hg.2.2.1.le) hg.2.2.2.1
    (by positivity) hg.2.2.2.2 (graftedDeformationRadius_encloses d t ht) j

/-- The grafted level loop meets the vertical line `Re z = x₀` exactly at the conjugate saddle
pair. -/
theorem nativeGraftedLevelLoop_vertical_pair {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t tmax eta x₀ : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (heta : 0 < eta) (hheight : eta ≤ levelHeight d t x₀)
    (z : ℂ) (hz : z ∈ range (nativeGraftedLevelLoop hN d t tmax eta x₀ ht)) :
    z.re = x₀ ↔ z = actualLevelGraphPoint d t x₀ ∨
      z = star (actualLevelGraphPoint d t x₀) := by
  have hg := graftedCentralGeometry hN d t tmax eta x₀ ht htmax heta hheight
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  exact actualGraftedLevelLoop_vertical_pair hN d t _ _ _ _ _ x₀ ht
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 (by positivity) z hz

/-- Both saddle points lie on the grafted level loop. -/
theorem nativeGraftedLevelLoop_contains_saddles {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t tmax eta x₀ : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (heta : 0 < eta) (hheight : eta ≤ levelHeight d t x₀) :
    actualLevelGraphPoint d t x₀ ∈ range (nativeGraftedLevelLoop hN d t tmax eta x₀ ht) ∧
      star (actualLevelGraphPoint d t x₀) ∈ range (nativeGraftedLevelLoop hN d t tmax eta x₀ ht) := by
  have hg := graftedCentralGeometry hN d t tmax eta x₀ ht htmax heta hheight
  exact actualGraftedLevelLoop_contains_saddles hN d t _ _ _ _ _ x₀ ht
    (le_trans hg.2.1.le hg.2.2.1.le) ⟨hg.2.1.le,hg.2.2.1.le⟩

end BlockBand.GaussianBulk
