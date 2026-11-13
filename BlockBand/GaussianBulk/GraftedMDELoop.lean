module
public import BlockBand.GaussianBulk.GraftedResolventWinding

/-!
# The grafted level loop at a solution of the finite MDE

Specializes the grafted level loop to the saddle `saddlePoint E t m` of a solution `m` of the
scalar finite MDE with `Im m ≥ v`, at height `η = tmin · v`. The resulting loop avoids every
pole, meets the saddle line exactly at the conjugate saddle pair, and has resolvent winding
integral `2πi` around every source point.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set MeasureTheory

/-- The level graph over the real part of the MDE saddle point passes through the saddle point. -/
theorem actualLevelGraphPoint_at_MDE {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t : ℝ) (m : ℂ) (ht : 0 < t) (hm : 0 < m.im)
    (hMDE : FiniteMDE d E t m) :
    actualLevelGraphPoint d t (saddlePoint E t m).re = saddlePoint E t m := by
  apply Complex.ext
  · simp [actualLevelGraphPoint]
  · simpa [actualLevelGraphPoint] using levelHeight_at_saddle hN d E t m ht hm hMDE

/-- At an MDE solution with `Im m ≥ v` and `t ≥ tmin`, the level height at the saddle is at
least `tmin · v`. -/
theorem actualLevelGraphPoint_MDE_bulk_height {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmin v : ℝ) (m : ℂ) (htmin : 0 < tmin)
    (ht : tmin ≤ t) (hv : 0 < v) (hm : v ≤ m.im) (hMDE : FiniteMDE d E t m) :
    tmin*v ≤ levelHeight d t (saddlePoint E t m).re := by
  rw [levelHeight_at_saddle hN d E t m (lt_of_lt_of_le htmin ht)
    (lt_of_lt_of_le hv hm) hMDE]
  exact saddlePoint_im_lower E t tmin v m htmin ht hv.le hm

/-- The grafted level loop at the MDE saddle, with height `η = tmin · v`. -/
def nativeMDEGraftedLevelLoop {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmin tmax v : ℝ) (m : ℂ) (htmin : 0 < tmin) (ht : tmin ≤ t) :=
  nativeGraftedLevelLoop hN d t tmax (tmin*v) (saddlePoint E t m).re
    (lt_of_lt_of_le htmin ht)

/-- The MDE grafted loop avoids every source pole. -/
theorem nativeMDEGraftedLevelLoop_ne_pole {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmin tmax v : ℝ) (m : ℂ) (htmin : 0 < tmin)
    (ht : tmin ≤ t) (htmax : t ≤ tmax) (hv : 0 < v) (hm : v ≤ m.im)
    (hMDE : FiniteMDE d E t m) (j : Fin N) :
    ∀ z ∈ range (nativeMDEGraftedLevelLoop hN d E t tmin tmax v m htmin ht),
      z ≠ (d j : ℂ) := by
  exact nativeGraftedLevelLoop_ne_pole hN d t tmax (tmin*v) _
    (lt_of_lt_of_le htmin ht) htmax (mul_pos htmin hv)
    (actualLevelGraphPoint_MDE_bulk_height hN d E t tmin v m htmin ht hv hm hMDE) j

/-- Both conjugate MDE saddle points lie on the loop. -/
theorem nativeMDEGraftedLevelLoop_contains_saddles {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmin tmax v : ℝ) (m : ℂ) (htmin : 0 < tmin)
    (ht : tmin ≤ t) (htmax : t ≤ tmax) (hv : 0 < v) (hm : v ≤ m.im)
    (hMDE : FiniteMDE d E t m) :
    saddlePoint E t m ∈ range (nativeMDEGraftedLevelLoop hN d E t tmin tmax v m htmin ht) ∧
      star (saddlePoint E t m) ∈ range (nativeMDEGraftedLevelLoop hN d E t tmin tmax v m htmin ht) := by
  have hh := nativeGraftedLevelLoop_contains_saddles hN d t tmax (tmin*v) _
    (lt_of_lt_of_le htmin ht) htmax (mul_pos htmin hv)
    (actualLevelGraphPoint_MDE_bulk_height hN d E t tmin v m htmin ht hv hm hMDE)
  rw [actualLevelGraphPoint_at_MDE hN d E t m (lt_of_lt_of_le htmin ht)
    (lt_of_lt_of_le hv hm) hMDE] at hh
  exact hh

/-- The MDE grafted loop meets the saddle vertical line only at the saddle and its conjugate. -/
theorem nativeMDEGraftedLevelLoop_vertical_pair {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmin tmax v : ℝ) (m : ℂ) (htmin : 0 < tmin)
    (ht : tmin ≤ t) (htmax : t ≤ tmax) (hv : 0 < v) (hm : v ≤ m.im)
    (hMDE : FiniteMDE d E t m) (z : ℂ)
    (hz : z ∈ range (nativeMDEGraftedLevelLoop hN d E t tmin tmax v m htmin ht)) :
    z.re = (saddlePoint E t m).re ↔ z = saddlePoint E t m ∨ z = star (saddlePoint E t m) := by
  have hh := nativeGraftedLevelLoop_vertical_pair hN d t tmax (tmin*v) _
    (lt_of_lt_of_le htmin ht) htmax (mul_pos htmin hv)
    (actualLevelGraphPoint_MDE_bulk_height hN d E t tmin v m htmin ht hv hm hMDE) z hz
  rw [actualLevelGraphPoint_at_MDE hN d E t m (lt_of_lt_of_le htmin ht)
    (lt_of_lt_of_le hv hm) hMDE] at hh
  exact hh

/-- The resolvent form `dz/(z - d_j)` is curve integrable on the MDE grafted loop, with integral
`2πi` for every source point `d_j`. -/
theorem nativeMDEGraftedLevelLoop_resolvent {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmin tmax v : ℝ) (m : ℂ) (htmin : 0 < tmin)
    (ht : tmin ≤ t) (htmax : t ≤ tmax) (hv : 0 < v) (hm : v ≤ m.im)
    (hMDE : FiniteMDE d E t m) (j : Fin N) :
    CurveIntegrable (graftedResolventForm (d j))
      (nativeMDEGraftedLevelLoop hN d E t tmin tmax v m htmin ht) ∧
      curveIntegral (graftedResolventForm (d j))
        (nativeMDEGraftedLevelLoop hN d E t tmin tmax v m htmin ht) = 2*(Real.pi : ℂ)*Complex.I := by
  exact nativeGraftedLevelLoop_resolvent hN d t tmax (tmin*v) _
    (lt_of_lt_of_le htmin ht) htmax (mul_pos htmin hv)
    (actualLevelGraphPoint_MDE_bulk_height hN d E t tmin v m htmin ht hv hm hMDE) j

end BlockBand.GaussianBulk
