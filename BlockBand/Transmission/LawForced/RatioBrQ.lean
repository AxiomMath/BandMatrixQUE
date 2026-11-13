module

public import BlockBand.Transmission.LawForced.RatioPoint

/-!
# The `κ ≡ 0` one-layer brackets: the quadratic and variance terms

Abstract law `μ`, `U`, `0 ⪯ T ⪯ I`, a covariance bound `hcov` of PCB's shape with real
`a`, complex `σ, σ'`, source `f` and error `ε`. Write `g = Re Tr T`, `hs = hs(T,f)`,
`τ = ‖Tr(Tf)‖ + √g·hs`, `Λ̂ = Σx_i + Σy_i/(1−y_i)` (`lamHat`).
* `dualLam_le_lamHat`, `sum_t_dualLam_le`: `0 ≤ Λ_z(t) ≤ Λ̂` on `[0,1]`, `Σt_kΛ_k ≤ Λ̂g`;
* **`covQ_sub_le`** (one weight point): `|Re covQ(w) − a·quadMain(w)| ≤ εΦ²g² + (‖σ‖+‖σ'‖)τ_w²`,
  `τ_w = ‖Tr(Tf)‖ + L√g·hs`, when `|r_k| ≤ Φ`, `|r_k − 1| ≤ Lt_k`;
* **`quadMean_sub_le`**: `|quadMean − aΣ_i(x_i²/2·quadMain(x_i) − y_i²/2·quadMain(−y_i))| ≤
  quadK·(εg² + (‖σ‖+‖σ'‖)(1+Λ̂)²τ²)`;
* **`covV_sub_le`**: `|Re covV/2 − aΣt²(1−t)Λ²| ≤ ((‖σ‖+‖σ'‖)Λ̂²hs² + εΛ̂²g²)/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {p W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}

/-- `Λ̂ = Σx_i + Σy_i/(1−y_i)`. -/
def lamHat (z : DualCoord p) : ℝ := ∑ i, z.1 i + ∑ i, z.2 i / (1 - z.2 i)

theorem lamHat_nonneg {z : DualCoord p} (hz : IsRatioRange z.1 z.2) : 0 ≤ lamHat z :=
  add_nonneg (Finset.sum_nonneg fun i _ => hz.1 i) (Finset.sum_nonneg fun i _ =>
    div_nonneg (hz.2 i).1 (by linarith [(hz.2 i).2]))

theorem x_le_lamHat {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (i : Fin p) :
    z.1 i ≤ lamHat z := by
  have h1 := Finset.single_le_sum (f := z.1) (fun j _ => hz.1 j) (Finset.mem_univ i)
  have h2 : 0 ≤ ∑ i, z.2 i / (1 - z.2 i) := Finset.sum_nonneg fun i _ =>
    div_nonneg (hz.2 i).1 (by linarith [(hz.2 i).2])
  unfold lamHat; linarith

theorem y_le_lamHat {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (i : Fin p) :
    z.2 i / (1 - z.2 i) ≤ lamHat z := by
  have h1 := Finset.single_le_sum (f := fun j => z.2 j / (1 - z.2 j))
    (fun j _ => div_nonneg (hz.2 j).1 (by linarith [(hz.2 j).2])) (Finset.mem_univ i)
  have h2 : 0 ≤ ∑ i, z.1 i := Finset.sum_nonneg fun i _ => hz.1 i
  unfold lamHat; linarith

theorem dualLam_le_lamHat {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : dualLam z t ≤ lamHat z := by
  unfold dualLam lamHat
  refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun i _ => ?_)
  · have hx := hz.1 i
    exact div_le_self hx (by nlinarith)
  · have hy0 := (hz.2 i).1
    have hy1 := (hz.2 i).2
    exact div_le_div_of_nonneg_left hy0 (by linarith) (by nlinarith)

theorem abs_dualLam_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : |dualLam z t| ≤ lamHat z := by
  rw [abs_of_nonneg (dualLam_nonneg hz ht0 ht1)]; exact dualLam_le_lamHat hz ht0 ht1

theorem sum_t_dualLam_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {n : Type*} [Fintype n]
    {t : n → ℝ} (ht0 : ∀ k, 0 ≤ t k) (ht1 : ∀ k, t k ≤ 1) :
    0 ≤ ∑ k, t k * dualLam z (t k) ∧ ∑ k, t k * dualLam z (t k) ≤ lamHat z * ∑ k, t k := by
  refine ⟨Finset.sum_nonneg fun k _ => mul_nonneg (ht0 k) (dualLam_nonneg hz (ht0 k) (ht1 k)), ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => by
    rw [mul_comm (lamHat z)]; exact mul_le_mul_of_nonneg_left (dualLam_le_lamHat hz (ht0 k) (ht1 k))
      (ht0 k)

/-- **One weight point of the quadratic mean.** -/
theorem covQ_sub_le (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (f : Matrix (Fin W) (Fin W) ℂ) (a : ℝ) (σ σ' : ℂ) {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      ((a : ℂ) * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - T) + crossedTensor v₁ v₂ v₃ v₄ (1 - T) 1) +
        σ * crossedTensor v₁ v₂ v₃ v₄ f f + σ' * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
      ε * fourNorm v₁ v₂ v₃ v₄) (w : ℝ) {Φ L : ℝ} (hL : 0 ≤ L)
    (hΦ : ∀ k, |(1 + w * ts_lam hT k)⁻¹| ≤ Φ)
    (hLk : ∀ k, |(1 + w * ts_lam hT k)⁻¹ - 1| ≤ L * ts_lam hT k) :
    |(covQ μ hT U w).re - a * quadMain (ts_lam hT) w| ≤
      ε * Φ ^ 2 * T.trace.re ^ 2 + (‖σ‖ + ‖σ'‖) *
        (‖(T * f).trace‖ + L * (Real.sqrt T.trace.re * hsSandwich T f)) ^ 2 := by
  set t := ts_lam hT
  set r : Fin W → ℝ := fun k => (1 + w * t k)⁻¹
  set fe := ts_ent hT f
  set N : ℂ := ∑ k, ((t k * r k : ℝ) : ℂ) * fe k k
  have hN := norm_sum_weight_fd_le hT ht1 f (φ₀ := 1) hL hLk
  rw [abs_one, one_mul] at hN
  have hc := cov_cross_contract hT U f (a : ℂ) σ σ' hcov (φ := r) hΦ
  have e : ∑ i, ∑ m, ((t i * r i * (t m * r m) : ℝ) : ℂ) *
      (bilinearCovariance μ U (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) (ts_vec hT i) -
        ((a : ℂ) * ((2 - t i - t m : ℝ) : ℂ) + σ * (fe i i * fe m m) +
          σ' * (conj (fe i i) * conj (fe m m)))) =
      covQ μ hT U w - ((a * quadMain t w : ℝ) : ℂ) - σ * N ^ 2 - σ' * (conj N) ^ 2 := by
    have hcN : conj N = ∑ k, ((t k * r k : ℝ) : ℂ) * conj (fe k k) := by
      simp only [N, map_sum, map_mul, Complex.conj_ofReal]
    rw [hcN, sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, covQ, quadMain]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [r]; push_cast; ring
  rw [e] at hc
  have hre : (covQ μ hT U w).re - a * quadMain t w =
      (covQ μ hT U w - ((a * quadMain t w : ℝ) : ℂ)).re := by
    rw [Complex.sub_re, Complex.ofReal_re]
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans ?_
  have hsplit : covQ μ hT U w - ((a * quadMain t w : ℝ) : ℂ) =
      (covQ μ hT U w - ((a * quadMain t w : ℝ) : ℂ) - σ * N ^ 2 - σ' * (conj N) ^ 2) +
        (σ * N ^ 2 + σ' * (conj N) ^ 2) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add hc ?_)
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← add_mul]
  have h0 := norm_nonneg N
  have := pow_le_pow_left₀ h0 hN 2
  exact mul_le_mul_of_nonneg_left this (by positivity)

theorem rx_bounds {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    |(1 + x * t)⁻¹| ≤ 1 ∧ |(1 + x * t)⁻¹ - 1| ≤ x * t := by
  have hp : 0 < 1 + x * t := by nlinarith
  have hi : (1 + x * t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hi0 : 0 < (1 + x * t)⁻¹ := inv_pos.2 hp
  have e : (1 + x * t)⁻¹ - 1 = -((1 + x * t)⁻¹ * (x * t)) := by
    have := inv_mul_cancel₀ hp.ne'
    linear_combination this
  refine ⟨by rw [abs_of_pos hi0]; exact hi, ?_⟩
  rw [e, abs_neg, abs_of_nonneg (mul_nonneg hi0.le (mul_nonneg hx ht))]
  calc (1 + x * t)⁻¹ * (x * t) ≤ 1 * (x * t) :=
        mul_le_mul_of_nonneg_right hi (mul_nonneg hx ht)
    _ = x * t := one_mul _

theorem ry_bounds {y t : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |(1 + -y * t)⁻¹| ≤ (1 - y)⁻¹ ∧ |(1 + -y * t)⁻¹ - 1| ≤ y / (1 - y) * t := by
  have e1 : 1 + -y * t = 1 - y * t := by ring
  rw [e1]
  have hp : 0 < 1 - y * t := by nlinarith
  have hy : 0 < 1 - y := by linarith
  have hi : (1 - y * t)⁻¹ ≤ (1 - y)⁻¹ := inv_anti₀ hy (by nlinarith)
  have hi0 : 0 < (1 - y * t)⁻¹ := inv_pos.2 hp
  have e : (1 - y * t)⁻¹ - 1 = (1 - y * t)⁻¹ * (y * t) := by
    have := inv_mul_cancel₀ hp.ne'
    linear_combination this
  refine ⟨by rw [abs_of_pos hi0]; exact hi, ?_⟩
  rw [e, abs_of_nonneg (mul_nonneg hi0.le (mul_nonneg hy0 ht))]
  calc (1 - y * t)⁻¹ * (y * t) ≤ (1 - y)⁻¹ * (y * t) :=
        mul_le_mul_of_nonneg_right hi (mul_nonneg hy0 ht)
    _ = y / (1 - y) * t := by rw [div_eq_mul_inv]; ring

theorem tauL_le {τ₀ L h Λ : ℝ} (hτ : 0 ≤ τ₀) (h0 : 0 ≤ h) (hL0 : 0 ≤ L) (hL : L ≤ Λ) :
    (τ₀ + L * h) ^ 2 ≤ ((1 + Λ) * (τ₀ + h)) ^ 2 := by
  have : τ₀ + L * h ≤ (1 + Λ) * (τ₀ + h) := by nlinarith
  exact pow_le_pow_left₀ (by positivity) this 2

/-- **The quadratic bracket.** -/
theorem quadMean_sub_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (hT : T.PosSemidef)
    (ht1 : ∀ i, ts_lam hT i ≤ 1) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (f : Matrix (Fin W) (Fin W) ℂ) (a : ℝ) (σ σ' : ℂ) {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      ((a : ℂ) * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - T) + crossedTensor v₁ v₂ v₃ v₄ (1 - T) 1) +
        σ * crossedTensor v₁ v₂ v₃ v₄ f f + σ' * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
      ε * fourNorm v₁ v₂ v₃ v₄) :
    |quadMean μ hT U z - a * ∑ i, (z.1 i ^ 2 / 2 * quadMain (ts_lam hT) (z.1 i) -
        z.2 i ^ 2 / 2 * quadMain (ts_lam hT) (-z.2 i))| ≤
      quadK z * (ε * T.trace.re ^ 2 + (‖σ‖ + ‖σ'‖) * ((1 + lamHat z) *
        (‖(T * f).trace‖ + Real.sqrt T.trace.re * hsSandwich T f)) ^ 2) := by
  set t := ts_lam hT
  have ht0 := ts_lam_nonneg hT
  set K := ε * T.trace.re ^ 2 + (‖σ‖ + ‖σ'‖) * ((1 + lamHat z) *
    (‖(T * f).trace‖ + Real.sqrt T.trace.re * hsSandwich T f)) ^ 2
  have hτ := norm_nonneg (T * f).trace
  have hh : 0 ≤ Real.sqrt T.trace.re * hsSandwich T f :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hS : 0 ≤ ‖σ‖ + ‖σ'‖ := by positivity
  have hx : ∀ i, |(covQ μ hT U (z.1 i)).re - a * quadMain t (z.1 i)| ≤ K := fun i => by
    have h := covQ_sub_le hT ht1 U f a σ σ' hcov (z.1 i) (Φ := 1) (hz.1 i)
      (fun k => (rx_bounds (hz.1 i) (ht0 k)).1) (fun k => (rx_bounds (hz.1 i) (ht0 k)).2)
    refine h.trans ?_
    rw [one_pow, mul_one]
    have := tauL_le hτ hh (hz.1 i) (x_le_lamHat hz i)
    simp only [K]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left this hS)
  have hy : ∀ i, |(covQ μ hT U (-z.2 i)).re - a * quadMain t (-z.2 i)| ≤
      ((1 - z.2 i)⁻¹) ^ 2 * K := fun i => by
    have hy0 := (hz.2 i).1
    have hy1 := (hz.2 i).2
    have hL0 : 0 ≤ z.2 i / (1 - z.2 i) := div_nonneg hy0 (by linarith)
    have h := covQ_sub_le hT ht1 U f a σ σ' hcov (-z.2 i) hL0
      (fun k => (ry_bounds hy0 hy1 (ht0 k) (ht1 k)).1)
      (fun k => (ry_bounds hy0 hy1 (ht0 k) (ht1 k)).2)
    refine h.trans ?_
    have h1 : 1 ≤ ((1 - z.2 i)⁻¹) ^ 2 := one_le_pow₀ (one_le_inv₀ (by linarith) |>.2 (by linarith))
    have := tauL_le hτ hh hL0 (y_le_lamHat hz i)
    have hK2 : 0 ≤ (‖σ‖ + ‖σ'‖) * ((1 + lamHat z) *
        (‖(T * f).trace‖ + Real.sqrt T.trace.re * hsSandwich T f)) ^ 2 := by positivity
    have : (‖σ‖ + ‖σ'‖) * (‖(T * f).trace‖ + z.2 i / (1 - z.2 i) *
        (Real.sqrt T.trace.re * hsSandwich T f)) ^ 2 ≤ ((1 - z.2 i)⁻¹) ^ 2 * ((‖σ‖ + ‖σ'‖) *
        ((1 + lamHat z) * (‖(T * f).trace‖ + Real.sqrt T.trace.re * hsSandwich T f)) ^ 2) :=
      (mul_le_mul_of_nonneg_left this hS).trans (le_mul_of_one_le_left hK2 h1)
    simp only [K, mul_add]
    nlinarith [sq_nonneg T.trace.re]
  have e : quadMean μ hT U z - a * ∑ i, (z.1 i ^ 2 / 2 * quadMain t (z.1 i) -
      z.2 i ^ 2 / 2 * quadMain t (-z.2 i)) = ∑ i, (z.1 i ^ 2 / 2 *
        ((covQ μ hT U (z.1 i)).re - a * quadMain t (z.1 i)) - z.2 i ^ 2 / 2 *
        ((covQ μ hT U (-z.2 i)).re - a * quadMain t (-z.2 i))) := by
    rw [quadMean, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, quadK, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z.1 i ^ 2 / 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ z.2 i ^ 2 / 2), add_mul]
  refine add_le_add (mul_le_mul_of_nonneg_left (hx i) (by positivity)) ?_
  calc z.2 i ^ 2 / 2 * |_| ≤ z.2 i ^ 2 / 2 * (((1 - z.2 i)⁻¹) ^ 2 * K) :=
        mul_le_mul_of_nonneg_left (hy i) (by positivity)
    _ = _ := by ring

/-- **The variance bracket.** -/
theorem covV_sub_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (hT : T.PosSemidef)
    (ht1 : ∀ i, ts_lam hT i ≤ 1) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (f : Matrix (Fin W) (Fin W) ℂ) (a : ℝ) (σ σ' : ℂ) {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      ((a : ℂ) * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - T) + crossedTensor v₁ v₂ v₃ v₄ (1 - T) 1) +
        σ * crossedTensor v₁ v₂ v₃ v₄ f f + σ' * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
      ε * fourNorm v₁ v₂ v₃ v₄) :
    |(covV μ hT U z).re / 2 -
        a * ∑ k, ts_lam hT k ^ 2 * (1 - ts_lam hT k) * dualLam z (ts_lam hT k) ^ 2| ≤
      ((‖σ‖ + ‖σ'‖) * lamHat z ^ 2 * hsSandwich T f ^ 2 +
        ε * lamHat z ^ 2 * T.trace.re ^ 2) / 2 := by
  set t := ts_lam hT
  have ht0 := ts_lam_nonneg hT
  have h := cov_diag_contract hT ht1 U f a σ σ' hcov (φ := fun k => dualLam z (t k))
    (fun k => abs_dualLam_le hz (ht0 k) (ht1 k))
  have hs : ∑ k, t k ^ 2 * (1 - t k) * dualLam z (t k) ^ 2 =
      ∑ k, t k ^ 2 * dualLam z (t k) ^ 2 * (1 - t k) :=
    Finset.sum_congr rfl fun k _ => by ring
  have e : (covV μ hT U z).re / 2 - a * ∑ k, t k ^ 2 * (1 - t k) * dualLam z (t k) ^ 2 =
      (covV μ hT U z - ((2 * a * ∑ k, t k ^ 2 * dualLam z (t k) ^ 2 * (1 - t k) : ℝ) : ℂ)).re /
        2 := by
    rw [Complex.sub_re, Complex.ofReal_re, hs]; ring
  rw [e, abs_div, abs_two]
  refine div_le_div_of_nonneg_right ((Complex.abs_re_le_norm _).trans ?_) zero_le_two
  exact h

end BlockBand.Transmission.LawForced
