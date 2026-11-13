module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import BlockBand.Coarea.Native.BlockBand.Analysis.PositiveResolvent

/-!
# Finite atomic Herglotz functions

* `AtomicHerglotz r`: Hermitian constant `const` and finitely supported PSD residues
  `residue : ℝ →₀ Matrix`, i.e. `μ = Σ_{x ∈ supp} δ_x residue x`. Coincident atoms are merged.
  The pole set is `residue.support`.
* `AtomicHerglotz.eval F z = const + Σ_x (x - z)⁻¹ residue x`, for every `z : ℂ`. For real `z`
  off the poles this is the boundary value; at a pole Lean's `0⁻¹ = 0` gives a conventional value.
* `AtomicHerglotz.atomSum F f = Σ_x f (x, residue x)`: vague coordinates of the marked pole
  configuration `Σ_x δ_{(x, residue x)}` on `ℝ × Matrix`.
* `ScalarAtomicHerglotz`, `AtomicHerglotz.scalar F v`: the quadratic form `v^* F v` is a scalar
  atomic Herglotz function with real constant `v^* C v` and weights `v^* residue x v ≥ 0`
  (`quadForm_eq_seval`).
* Positivity: `seval_im`, `seval_im_nonneg`, `seval_ofReal_im` (real boundary values),
  `matrixImaginaryPart_eval` and `matrixImaginaryPart_eval_posSemidef`
  (`Im F(z) = Σ_x Im z/|x - z|² residue x ⪰ 0`).
* `norm_seval_sub_seval_I_le` (Harnack-type bound, the analytic-topology tightness step): `|q(z) - q(i)| ≤ |z - i| √(max 2 ((1+2(Re z)²)/(Im z)²)) Im q(i)`.
* `analyticAt_seval`, `continuousAt_seval`: analytic off the poles.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Complex Matrix
open scoped ComplexOrder

namespace BlockBand.Critical.Herglotz

/-- A finite atomic `r × r` matrix Herglotz function `C + ∫ (x - z)⁻¹ μ(dx)`:
`const = C` is Hermitian and `μ = Σ_{x ∈ residue.support} δ_x residue x` is a finite atomic
positive semidefinite matrix measure on `ℝ`. -/
structure AtomicHerglotz (r : ℕ) where
  /-- The Hermitian constant `C`. -/
  const : Matrix (Fin r) (Fin r) ℂ
  const_isHermitian : const.IsHermitian
  /-- The matrix residues `μ({x})`; finitely supported. -/
  residue : ℝ →₀ Matrix (Fin r) (Fin r) ℂ
  residue_posSemidef : ∀ x, (residue x).PosSemidef

/-- A finite atomic scalar Herglotz function `c + Σ_x a_x / (x - z)`, `c` real, `a_x ≥ 0`. -/
structure ScalarAtomicHerglotz where
  /-- The real constant. -/
  const : ℝ
  /-- The atom weights. -/
  weight : ℝ →₀ ℝ
  weight_nonneg : ∀ x, 0 ≤ weight x

namespace ScalarAtomicHerglotz

/-- Value `c + Σ_x a_x (x - z)⁻¹` at any `z : ℂ` (Lean's `0⁻¹ = 0` at a real pole). -/
def seval (q : ScalarAtomicHerglotz) (z : ℂ) : ℂ :=
  (q.const : ℂ) + q.weight.sum fun x a => (a : ℂ) * ((x : ℂ) - z)⁻¹

theorem im_inv_ofReal_sub (x : ℝ) (z : ℂ) :
    (((x : ℂ) - z)⁻¹).im = z.im / Complex.normSq ((x : ℂ) - z) := by
  rw [Complex.inv_im]
  simp

/-- `Im q(z) = Σ_x a_x Im z / |x - z|²`. -/
theorem seval_im (q : ScalarAtomicHerglotz) (z : ℂ) :
    (q.seval z).im = q.weight.sum fun x a => a * (z.im / Complex.normSq ((x : ℂ) - z)) := by
  unfold seval
  rw [Complex.add_im, Complex.ofReal_im, zero_add]
  unfold Finsupp.sum
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.im_ofReal_mul, im_inv_ofReal_sub]

/-- Positivity of the imaginary part on the closed upper half-plane. -/
theorem seval_im_nonneg (q : ScalarAtomicHerglotz) {z : ℂ} (hz : 0 ≤ z.im) :
    0 ≤ (q.seval z).im := by
  rw [seval_im]
  unfold Finsupp.sum
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (q.weight_nonneg x) (div_nonneg hz (Complex.normSq_nonneg _))

/-- Boundary values on the real line (off the poles, and by convention at the poles) are real. -/
theorem seval_ofReal_im (q : ScalarAtomicHerglotz) (x : ℝ) : (q.seval x).im = 0 := by
  rw [seval_im]
  simp

/-- `Im q(i) = Σ_x a_x / (1 + x²)`. -/
theorem seval_I_im (q : ScalarAtomicHerglotz) :
    (q.seval I).im = q.weight.sum fun x a => a / (1 + x ^ 2) := by
  rw [seval_im]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun x _ => ?_
  show q.weight x * (I.im / Complex.normSq ((x : ℂ) - I)) = q.weight x / (1 + x ^ 2)
  rw [Complex.normSq_apply]
  simp
  ring

/-- `q` is analytic at every `z` that is not a pole. -/
theorem analyticAt_seval (q : ScalarAtomicHerglotz) {z : ℂ}
    (hz : ∀ x ∈ q.weight.support, (x : ℂ) ≠ z) : AnalyticAt ℂ q.seval z := by
  unfold seval Finsupp.sum
  refine analyticAt_const.add ?_
  have : (fun w : ℂ => ∑ x ∈ q.weight.support, (q.weight x : ℂ) * ((x : ℂ) - w)⁻¹) =
      ∑ x ∈ q.weight.support, fun w : ℂ => (q.weight x : ℂ) * ((x : ℂ) - w)⁻¹ := by
    funext w; simp
  rw [this]
  refine Finset.analyticAt_sum _ fun x hx => ?_
  exact analyticAt_const.mul ((analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.mpr (hz x hx)))

/-- `q` is analytic off the real line. -/
theorem analyticAt_seval_of_im_ne (q : ScalarAtomicHerglotz) {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ q.seval z :=
  q.analyticAt_seval fun x _ h => hz (by rw [← h]; simp)

theorem continuousAt_seval (q : ScalarAtomicHerglotz) {z : ℂ}
    (hz : ∀ x ∈ q.weight.support, (x : ℂ) ≠ z) : ContinuousAt q.seval z :=
  (q.analyticAt_seval hz).continuousAt

/-- Pointwise kernel comparison behind the Harnack bound: for `Im z > 0`,
`|(x - z)⁻¹ - (x - i)⁻¹| ≤ |z - i| √K / (1 + x²)` with `K = max 2 ((1+2(Re z)²)/(Im z)²)`. -/
theorem norm_inv_sub_sub_inv_I_le {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    ‖((x : ℂ) - z)⁻¹ - ((x : ℂ) - I)⁻¹‖ ≤
      ‖z - I‖ * Real.sqrt (max 2 ((1 + 2 * z.re ^ 2) / z.im ^ 2)) / (1 + x ^ 2) := by
  set K : ℝ := max 2 ((1 + 2 * z.re ^ 2) / z.im ^ 2) with hKdef
  have hK2 : 2 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hxz : (x : ℂ) - z ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hxI : (x : ℂ) - I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hid : ((x : ℂ) - z)⁻¹ - ((x : ℂ) - I)⁻¹ = (z - I) / (((x : ℂ) - z) * ((x : ℂ) - I)) := by
    field_simp
    ring
  have hnI : ‖(x : ℂ) - I‖ = Real.sqrt (1 + x ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp
    ring
  have hnz : ‖(x : ℂ) - z‖ = Real.sqrt ((x - z.re) ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp
    ring
  -- `K ((x - a)² + b²) ≥ 1 + x²`.
  have hlow : 1 + x ^ 2 ≤ K * ((x - z.re) ^ 2 + z.im ^ 2) := by
    have hb2 : 0 < z.im ^ 2 := by positivity
    have h1 : (1 + 2 * z.re ^ 2) / z.im ^ 2 ≤ K := le_max_right _ _
    have h1' : 1 + 2 * z.re ^ 2 ≤ K * z.im ^ 2 := by
      rwa [div_le_iff₀ hb2] at h1
    nlinarith [sq_nonneg (x - 2 * z.re)]
  rw [hid, norm_div, norm_mul, hnI, hnz]
  have hx1 : 0 < 1 + x ^ 2 := by positivity
  have hq : 0 < (x - z.re) ^ 2 + z.im ^ 2 := by positivity
  have hs1 := Real.sqrt_pos.mpr hx1
  have hs2 := Real.sqrt_pos.mpr hq
  rw [div_le_div_iff₀ (mul_pos hs2 hs1) hx1]
  -- `(1+x²) ≤ √K √q √(1+x²)`, since `√(1+x²) ≤ √(K q)`.
  have hsK : Real.sqrt (1 + x ^ 2) ≤ Real.sqrt K * Real.sqrt ((x - z.re) ^ 2 + z.im ^ 2) := by
    rw [← Real.sqrt_mul hK0.le]
    exact Real.sqrt_le_sqrt hlow
  have hsq : Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + x ^ 2) = 1 + x ^ 2 :=
    Real.mul_self_sqrt hx1.le
  have hnzI : 0 ≤ ‖z - I‖ := norm_nonneg _
  have : 1 + x ^ 2 ≤ Real.sqrt K * (Real.sqrt ((x - z.re) ^ 2 + z.im ^ 2) *
      Real.sqrt (1 + x ^ 2)) := by nlinarith
  calc ‖z - I‖ * (1 + x ^ 2)
      ≤ ‖z - I‖ * (Real.sqrt K * (Real.sqrt ((x - z.re) ^ 2 + z.im ^ 2) *
          Real.sqrt (1 + x ^ 2))) := mul_le_mul_of_nonneg_left this hnzI
    _ = ‖z - I‖ * Real.sqrt K * (Real.sqrt ((x - z.re) ^ 2 + z.im ^ 2) *
          Real.sqrt (1 + x ^ 2)) := by ring

/-- **Harnack-type bound** (tightness in the analytic topology): for a scalar
finite atomic Herglotz function and `Im z > 0`,
`|q(z) - q(i)| ≤ |z - i| √(max 2 ((1+2(Re z)²)/(Im z)²)) · Im q(i)`. Constants are explicit and
locally bounded on the open upper half-plane; no constant term enters. -/
theorem norm_seval_sub_seval_I_le (q : ScalarAtomicHerglotz) {z : ℂ} (hz : 0 < z.im) :
    ‖q.seval z - q.seval I‖ ≤
      ‖z - I‖ * Real.sqrt (max 2 ((1 + 2 * z.re ^ 2) / z.im ^ 2)) * (q.seval I).im := by
  rw [seval_I_im]
  unfold seval Finsupp.sum
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (q.weight_nonneg x)]
  have h := norm_inv_sub_sub_inv_I_le hz x
  have hw := q.weight_nonneg x
  calc q.weight x * ‖((x : ℂ) - z)⁻¹ - ((x : ℂ) - I)⁻¹‖
      ≤ q.weight x * (‖z - I‖ * Real.sqrt (max 2 ((1 + 2 * z.re ^ 2) / z.im ^ 2)) /
          (1 + x ^ 2)) := mul_le_mul_of_nonneg_left h hw
    _ = _ := by ring

end ScalarAtomicHerglotz

namespace AtomicHerglotz

variable {r : ℕ}

/-- Value `C + Σ_x (x - z)⁻¹ μ({x})` at any `z : ℂ`; the Herglotz function for `Im z > 0`, the
boundary value at real `z` off the poles. -/
def eval (F : AtomicHerglotz r) (z : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  F.const + F.residue.sum fun x R => ((x : ℂ) - z)⁻¹ • R

/-- Vague coordinate `Σ_x f (x, μ({x}))` of the marked pole configuration. -/
def atomSum (F : AtomicHerglotz r)
    (f : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) : ℝ :=
  ∑ x ∈ F.residue.support, f (x, F.residue x)

/-- The quadratic form `v^* F(z) v`. -/
def quadForm (F : AtomicHerglotz r) (v : Fin r → ℂ) (z : ℂ) : ℂ :=
  star v ⬝ᵥ (F.eval z *ᵥ v)

theorem star_dotProduct_mulVec_ofReal_re {M : Matrix (Fin r) (Fin r) ℂ} (hM : M.IsHermitian)
    (v : Fin r → ℂ) : (((star v ⬝ᵥ (M *ᵥ v)).re : ℝ) : ℂ) = star v ⬝ᵥ (M *ᵥ v) := by
  apply Complex.ext
  · simp
  · simpa using (hM.im_star_dotProduct_mulVec_self v).symm

/-- The scalar atomic Herglotz function `v^* F v`: constant `Re(v^* C v)`, weights
`Re(v^* μ({x}) v) ≥ 0` (both are real). -/
def scalar (F : AtomicHerglotz r) (v : Fin r → ℂ) : ScalarAtomicHerglotz where
  const := (star v ⬝ᵥ (F.const *ᵥ v)).re
  weight := Finsupp.mapRange (fun R => (star v ⬝ᵥ (R *ᵥ v)).re) (by simp) F.residue
  weight_nonneg x := by
    simp only [Finsupp.mapRange_apply]
    exact (F.residue_posSemidef x).re_dotProduct_nonneg v

/-- `v^* F(z) v` is the scalar atomic Herglotz function `F.scalar v`, at every `z : ℂ`. -/
theorem quadForm_eq_seval (F : AtomicHerglotz r) (v : Fin r → ℂ) (z : ℂ) :
    F.quadForm v z = (F.scalar v).seval z := by
  unfold quadForm eval ScalarAtomicHerglotz.seval scalar
  simp only
  rw [Finsupp.sum_mapRange_index (by simp)]
  rw [Matrix.add_mulVec, dotProduct_add, star_dotProduct_mulVec_ofReal_re F.const_isHermitian]
  congr 1
  unfold Finsupp.sum
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  show _ = (((star v ⬝ᵥ (F.residue x *ᵥ v)).re : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹
  rw [Matrix.smul_mulVec, dotProduct_smul,
    star_dotProduct_mulVec_ofReal_re (F.residue_posSemidef x).isHermitian, smul_eq_mul, mul_comm]

/-- Boundary quadratic forms are real. -/
theorem quadForm_ofReal_im (F : AtomicHerglotz r) (v : Fin r → ℂ) (x : ℝ) :
    (F.quadForm v x).im = 0 := by
  rw [quadForm_eq_seval]
  exact (F.scalar v).seval_ofReal_im x

/-- Positivity of the quadratic forms on the closed upper half-plane. -/
theorem quadForm_im_nonneg (F : AtomicHerglotz r) (v : Fin r → ℂ) {z : ℂ} (hz : 0 ≤ z.im) :
    0 ≤ (F.quadForm v z).im := by
  rw [quadForm_eq_seval]
  exact (F.scalar v).seval_im_nonneg hz

open CoareaNative.BlockBand (matrixImaginaryPart)

/-- `Im F(z) = Σ_x (Im z / |x - z|²) μ({x})`, with `Im M = (M - Mᴴ)/(2i)`. -/
theorem matrixImaginaryPart_eval (F : AtomicHerglotz r) (z : ℂ) :
    matrixImaginaryPart (F.eval z) =
      F.residue.sum fun x R => ((z.im / Complex.normSq ((x : ℂ) - z) : ℝ) : ℂ) • R := by
  unfold matrixImaginaryPart eval Finsupp.sum
  rw [Matrix.conjTranspose_add, F.const_isHermitian.eq, Matrix.conjTranspose_sum,
    add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.conjTranspose_smul, (F.residue_posSemidef x).isHermitian.eq, ← sub_smul, smul_smul]
  congr 1
  rw [← ScalarAtomicHerglotz.im_inv_ofReal_sub]
  generalize ((x : ℂ) - z)⁻¹ = w
  apply Complex.ext
  · simp [Complex.mul_re]
    ring
  · simp [Complex.mul_im]

/-- `Im F(z) ⪰ 0` on the closed upper half-plane. -/
theorem matrixImaginaryPart_eval_posSemidef (F : AtomicHerglotz r) {z : ℂ} (hz : 0 ≤ z.im) :
    (matrixImaginaryPart (F.eval z)).PosSemidef := by
  rw [matrixImaginaryPart_eval]
  unfold Finsupp.sum
  refine Matrix.posSemidef_sum _ fun x _ => ?_
  have hc : (0 : ℂ) ≤ ((z.im / Complex.normSq ((x : ℂ) - z) : ℝ) : ℂ) := by
    exact_mod_cast div_nonneg hz (Complex.normSq_nonneg _)
  exact (F.residue_posSemidef x).smul hc

end AtomicHerglotz

end BlockBand.Critical.Herglotz
