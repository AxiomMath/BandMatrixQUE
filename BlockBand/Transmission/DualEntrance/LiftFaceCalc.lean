module

public import BlockBand.Transmission.DualLift.Flat
public import BlockBand.SourceProcess.Stochastic.Bridges.Structural

/-!
# The three faces of the flat dual and their entrance inequalities

Deterministic. The faces of the closed strip `{x ≥ 0, 0 ≤ y ≤ 1}` are `z = x`, `z = y`,
`z = 1 − y`, written as affine images `z = r·(x, y) + c` with rows `faceR i` and constants
`faceC i` (`i : Fin 3`). Along the flat `p = 1` dual characteristics (`flatDrift D₀ 1`,
`flatDiff D₀ 1 = diag(D₀x(1+x), D₀y(1−y))`) the face `z` has drift `b = r·β` and variance
`a = r₀²α₀₀ + r₁²α₁₁`.

**`face_ineq`**: on `{x ≥ 0, x ≤ m, 0 ≤ y ≤ 1, x + y ≥ ε}` (`ε > 0`, `m ≥ 0`, `D₀ > 0`)
every face satisfies the hypotheses of the generic one-dimensional entrance lemma
(`IsEntranceFace`) with `c = D₀/2`, `K = M = faceK = D₀(1+m)/ε + D₀`, `B = faceBd = D₀(1+m)`:
`a ≤ 2z(b + Kz)`, `c − Kz ≤ b ≤ B`. The corner `x = y = 0` is excluded by `x + y ≥ ε` (there
`K` blows up like `1/ε`); the stopping time `stopT` stops before `{x + y ≤ ε} ∪ {x ≥ m}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualEntrance

open BlockBand.Transmission.Dual BlockBand.Transmission.DualLift
open scoped Matrix

/-- The face rows `x`, `y`, `−y`. -/
def faceR : Fin 3 → Fin 2 → ℝ := ![![1, 0], ![0, 1], ![0, -1]]

/-- The face constants (`1 − y` has constant `1`). -/
def faceC : Fin 3 → ℝ := ![0, 0, 1]

/-- The face row as a `1 × 2` matrix. -/
def faceA (i : Fin 3) : Matrix (Fin 1) (Fin 2) ℝ := Matrix.of fun _ j => faceR i j

/-- The face constant as a vector of `ℝ¹`. -/
def faceB (i : Fin 3) : Fin 1 → ℝ := fun _ => faceC i

/-- The entrance constant `K = M`. -/
def faceK (D0 ε m : ℝ) : ℝ := D0 * (1 + m) / ε + D0

/-- The drift bound `B`. -/
def faceBd (D0 m : ℝ) : ℝ := D0 * (1 + m)

theorem faceA_mulVec (i : Fin 3) (v : Fin 2 → ℝ) (k : Fin 1) :
    (faceA i *ᵥ v) k = faceR i 0 * v 0 + faceR i 1 * v 1 := by
  simp [faceA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem face_apply (i : Fin 3) (v : Fin 2 → ℝ) (k : Fin 1) :
    (faceA i *ᵥ v + faceB i) k = faceR i 0 * v 0 + faceR i 1 * v 1 + faceC i := by
  rw [Pi.add_apply, faceA_mulVec]; rfl

theorem faceA_cov (i : Fin 3) (d : Fin 2 → ℝ) :
    (faceA i * Matrix.diagonal d * (faceA i)ᵀ) 0 0 =
      faceR i 0 ^ 2 * d 0 + faceR i 1 ^ 2 * d 1 := by
  rw [BlockBand.SourceProcess.Stochastic.Bridges.mul_mul_transpose_apply]
  simp [faceA, Fin.sum_univ_two, Matrix.diagonal_apply]
  ring

theorem face_nonneg (i : Fin 3) {z : Fin 2 → ℝ} (h0 : 0 ≤ z 0) (h1 : 0 ≤ z 1) (h1' : z 1 ≤ 1) :
    0 ≤ faceR i 0 * z 0 + faceR i 1 * z 1 + faceC i := by
  fin_cases i <;> simp [faceR, faceC] <;> linarith

theorem faceK_nonneg {D0 ε m : ℝ} (hD0 : 0 < D0) (hε : 0 < ε) (hm : 0 ≤ m) :
    0 ≤ faceK D0 ε m := by
  unfold faceK; positivity

/-!
## The three faces
-/

theorem inv_S_le {ε m x y : ℝ} (hε : 0 < ε) (hm : 0 ≤ m) (hS : ε ≤ x + y) :
    1 / (x + y) ≤ (1 + m) / ε :=
  div_le_div₀ (by linarith) (by linarith) hε hS

theorem faceX_ineq {D0 ε m x y : ℝ} (hD0 : 0 < D0) (hε : 0 < ε) (hm : 0 ≤ m) (hx : 0 ≤ x)
    (hxm : x ≤ m) (hS : ε ≤ x + y) :
    D0 * (x * (1 + x)) ≤
      2 * x * (D0 / 2 * (1 + 2 * x - 2 * x * (1 + x) / (x + y)) + faceK D0 ε m * x) ∧
    D0 / 2 - faceK D0 ε m * x ≤ D0 / 2 * (1 + 2 * x - 2 * x * (1 + x) / (x + y)) ∧
    D0 / 2 * (1 + 2 * x - 2 * x * (1 + x) / (x + y)) ≤ faceBd D0 m := by
  set L := (1 + m) / ε
  set q := (1 + x) / (x + y) with hq
  have hS0 : 0 < x + y := by linarith
  have hqL : q ≤ L := div_le_div₀ (by linarith) (by linarith) hε hS
  have hq0 : 0 ≤ q := by positivity
  have e : 2 * x * (1 + x) / (x + y) = 2 * x * q := by rw [hq]; ring
  have hK : faceK D0 ε m = D0 * L + D0 := by unfold faceK; ring
  rw [e, hK]
  have h1 := mul_nonneg (mul_nonneg (sq_nonneg x) hD0.le) (sub_nonneg.2 hqL)
  have h2 := mul_nonneg (mul_nonneg hx hD0.le) (sub_nonneg.2 hqL)
  have h3 := mul_nonneg (mul_nonneg hx hD0.le) hq0
  refine ⟨by nlinarith [mul_nonneg (sq_nonneg x) hD0.le], by nlinarith, ?_⟩
  unfold faceBd; nlinarith

theorem faceY_ineq {D0 ε m x y : ℝ} (hD0 : 0 < D0) (hε : 0 < ε) (hm : 0 ≤ m)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) (hS : ε ≤ x + y) :
    D0 * (y * (1 - y)) ≤
      2 * y * (D0 / 2 * (1 - 2 * y - 2 * y * (1 - y) / (x + y)) + faceK D0 ε m * y) ∧
    D0 / 2 - faceK D0 ε m * y ≤ D0 / 2 * (1 - 2 * y - 2 * y * (1 - y) / (x + y)) ∧
    D0 / 2 * (1 - 2 * y - 2 * y * (1 - y) / (x + y)) ≤ faceBd D0 m := by
  set L := (1 + m) / ε
  set t := 1 / (x + y) with ht
  have hS0 : 0 < x + y := by linarith
  have htL : t ≤ L := inv_S_le hε hm hS
  have ht0 : 0 ≤ t := by positivity
  have hp : (1 - y) * t ≤ L := by nlinarith
  have hp0 : 0 ≤ (1 - y) * t := mul_nonneg (by linarith) ht0
  have e : 2 * y * (1 - y) / (x + y) = 2 * y * ((1 - y) * t) := by rw [ht]; ring
  have hK : faceK D0 ε m = D0 * L + D0 := by unfold faceK; ring
  rw [e, hK]
  have h1 := mul_nonneg (mul_nonneg (sq_nonneg y) hD0.le) (sub_nonneg.2 hp)
  have h2 := mul_nonneg (mul_nonneg hy hD0.le) (sub_nonneg.2 hp)
  have h3 := mul_nonneg (mul_nonneg hy hD0.le) hp0
  refine ⟨by nlinarith [mul_nonneg (sq_nonneg y) hD0.le], by nlinarith, ?_⟩
  unfold faceBd; nlinarith

theorem faceW_ineq {D0 ε m x y : ℝ} (hD0 : 0 < D0) (hε : 0 < ε) (hm : 0 ≤ m) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) (hS : ε ≤ x + y) :
    D0 * (y * (1 - y)) ≤
      2 * (1 - y) * (-(D0 / 2 * (1 - 2 * y - 2 * y * (1 - y) / (x + y))) +
        faceK D0 ε m * (1 - y)) ∧
    D0 / 2 - faceK D0 ε m * (1 - y) ≤ -(D0 / 2 * (1 - 2 * y - 2 * y * (1 - y) / (x + y))) ∧
    -(D0 / 2 * (1 - 2 * y - 2 * y * (1 - y) / (x + y))) ≤ faceBd D0 m := by
  set L := (1 + m) / ε
  set p := y / (x + y) with hp
  have hS0 : 0 < x + y := by linarith
  have hL0 : 0 ≤ L := by positivity
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hS0]; linarith
  have e : 2 * y * (1 - y) / (x + y) = 2 * (1 - y) * p := by rw [hp]; ring
  have hK : faceK D0 ε m = D0 * L + D0 := by unfold faceK; ring
  rw [e, hK]
  have hw : 0 ≤ 1 - y := by linarith
  have h1 := mul_nonneg (mul_nonneg (sq_nonneg (1 - y)) hD0.le) hp0
  have h2 := mul_nonneg (mul_nonneg (sq_nonneg (1 - y)) hD0.le) hL0
  have h3 := mul_nonneg (mul_nonneg hw hD0.le) hp0
  have h4 := mul_nonneg (mul_nonneg hw hD0.le) hL0
  have h5 := mul_nonneg (mul_nonneg hw hD0.le) (sub_nonneg.2 hp1)
  refine ⟨by nlinarith [mul_nonneg (sq_nonneg (1 - y)) hD0.le], by nlinarith, ?_⟩
  unfold faceBd; nlinarith

/-- **The entrance inequalities on every face** (`c = D₀/2`, `K = M = faceK`, `B = faceBd`). -/
theorem face_ineq (i : Fin 3) {D0 ε m : ℝ} (hD0 : 0 < D0) (hε : 0 < ε) (hm : 0 ≤ m)
    {z : Fin 2 → ℝ} (h0 : 0 ≤ z 0) (h0m : z 0 ≤ m) (h1 : 0 ≤ z 1) (h1' : z 1 ≤ 1)
    (hS : ε ≤ z 0 + z 1) :
    faceR i 0 ^ 2 * (D0 * (z 0 * (1 + z 0))) + faceR i 1 ^ 2 * (D0 * (z 1 * (1 - z 1))) ≤
      2 * (faceR i 0 * z 0 + faceR i 1 * z 1 + faceC i) *
        ((faceR i 0 * flatDrift D0 1 z 0 + faceR i 1 * flatDrift D0 1 z 1) +
          faceK D0 ε m * (faceR i 0 * z 0 + faceR i 1 * z 1 + faceC i)) ∧
    D0 / 2 - faceK D0 ε m * (faceR i 0 * z 0 + faceR i 1 * z 1 + faceC i) ≤
      faceR i 0 * flatDrift D0 1 z 0 + faceR i 1 * flatDrift D0 1 z 1 ∧
    faceR i 0 * flatDrift D0 1 z 0 + faceR i 1 * flatDrift D0 1 z 1 ≤ faceBd D0 m := by
  rw [flatDrift_one_eq]
  fin_cases i <;> simp [faceR, faceC]
  · have h := faceX_ineq hD0 hε hm h0 h0m hS
    exact ⟨h.1, by linarith [h.2.1], h.2.2⟩
  · have h := faceY_ineq hD0 hε hm h1 h1' hS
    exact ⟨h.1, by linarith [h.2.1], h.2.2⟩
  · have h := faceW_ineq hD0 hε hm h0 h1 h1' hS
    exact ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2]⟩

end BlockBand.Transmission.DualEntrance
