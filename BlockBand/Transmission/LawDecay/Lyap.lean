module

public import BlockBand.Transmission.LawDecay.Taylor

/-!
# The regularised Lyapunov function and its one-step Taylor bound

The Lyapunov function `F = √g(1 - P₂/(64g²)) = g^{1/2} - P₂g^{-3/2}/64` has derivatives that
blow up at `g = 0`. Here `g` is shifted by `ε ∈ (0,1]`:
`Φ_ε(x, y) = (x+ε)^{1/2} - y(x+ε)^{-3/2}/64` (`lyap`), with `x = g = Tr T`, `y = P₂ = Tr T²`.
The coefficients of its second-order expansion are `coefX = ∂ₓΦ`, `coefY = ∂_yΦ`,
`coefXX = ∂ₓ²Φ/2`, `coefXY = ∂ₓ∂_yΦ` (`∂_y²Φ = 0`).

**`lyap_step`**: on the convex region `0 ≤ y ≤ x` (which contains `(g, P₂)`, since `0 ⪯ T ⪯ 1`),
with `h = x' - x`, `k = y' - y`,
`Φ(x',y') ≤ Φ(x,y) + coefX·h + coefY·k + coefXX·h² + coefXY·hk + ε^{-7/2}(|h|³ + h²|k|)/6`.
The third derivative of `t ↦ Φ((x,y) + t(h,k))` is bounded on `[0,1]` using `y + tk ≤ x + th`,
`x + th + ε ≥ ε` and `ε ≤ 1` (`taylor2_upper`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

/-- `Φ_ε(x, y) = (x+ε)^{1/2} - y(x+ε)^{-3/2}/64`. -/
def lyap (ε x y : ℝ) : ℝ := (x + ε) ^ (1 / 2 : ℝ) - y * (x + ε) ^ (-3 / 2 : ℝ) / 64

/-- `∂ₓΦ_ε`. -/
def coefX (ε x y : ℝ) : ℝ := (x + ε) ^ (-1 / 2 : ℝ) / 2 + 3 * y * (x + ε) ^ (-5 / 2 : ℝ) / 128

/-- `∂_yΦ_ε`. -/
def coefY (ε x : ℝ) : ℝ := -((x + ε) ^ (-3 / 2 : ℝ) / 64)

/-- `∂ₓ²Φ_ε / 2`. -/
def coefXX (ε x y : ℝ) : ℝ :=
  -((x + ε) ^ (-3 / 2 : ℝ) / 8) - 15 * y * (x + ε) ^ (-7 / 2 : ℝ) / 512

/-- `∂ₓ∂_yΦ_ε`. -/
def coefXY (ε x : ℝ) : ℝ := 3 * (x + ε) ^ (-5 / 2 : ℝ) / 128

theorem hasDerivAt_pw {x h ε p q : ℝ} (hq : q = p - 1) {t : ℝ} (hs : 0 < x + t * h + ε) :
    HasDerivAt (fun u => (x + u * h + ε) ^ p) (h * p * (x + t * h + ε) ^ q) t := by
  have h1 : HasDerivAt (fun u => x + u * h + ε) h t := by
    have := (((hasDerivAt_id' t).mul_const h).const_add x).add_const ε
    simpa using this
  rw [hq]; exact h1.rpow_const (Or.inl hs.ne')

theorem hasDerivAt_lin_pw {x y h k ε p q : ℝ} (hq : q = p - 1) {t : ℝ}
    (hs : 0 < x + t * h + ε) :
    HasDerivAt (fun u => (y + u * k) * (x + u * h + ε) ^ p)
      (k * (x + t * h + ε) ^ p + (y + t * k) * (h * p * (x + t * h + ε) ^ q)) t := by
  have h1 : HasDerivAt (fun u => y + u * k) k t := by
    simpa using ((hasDerivAt_id' t).mul_const k).const_add y
  exact h1.mul (hasDerivAt_pw hq hs)

/-- The first derivative of the segment function `t ↦ Φ((x,y) + t(h,k))`. -/
def seg1 (ε x y h k : ℝ) (t : ℝ) : ℝ :=
  coefX ε (x + t * h) (y + t * k) * h + coefY ε (x + t * h) * k

/-- The second derivative. -/
def seg2 (ε x y h k : ℝ) (t : ℝ) : ℝ :=
  2 * (coefXX ε (x + t * h) (y + t * k) * h ^ 2 + coefXY ε (x + t * h) * h * k)

/-- The third derivative. -/
def seg3 (ε x y h k : ℝ) (t : ℝ) : ℝ :=
  3 / 8 * h ^ 3 * (x + t * h + ε) ^ (-5 / 2 : ℝ) -
    45 / 256 * h ^ 2 * k * (x + t * h + ε) ^ (-7 / 2 : ℝ) +
    105 / 512 * (y + t * k) * h ^ 3 * (x + t * h + ε) ^ (-9 / 2 : ℝ)

theorem hasDerivAt_seg0 {ε x y h k t : ℝ} (hs : 0 < x + t * h + ε) :
    HasDerivAt (fun u => lyap ε (x + u * h) (y + u * k)) (seg1 ε x y h k t) t := by
  have a := hasDerivAt_pw (p := (1 / 2 : ℝ)) (q := (-1 / 2 : ℝ)) (by norm_num) hs
  have b := hasDerivAt_lin_pw (y := y) (k := k) (p := (-3 / 2 : ℝ)) (q := (-5 / 2 : ℝ))
    (by norm_num) hs
  show HasDerivAt (fun u => (x + u * h + ε) ^ (1 / 2 : ℝ) -
    (y + u * k) * (x + u * h + ε) ^ (-3 / 2 : ℝ) / 64) _ t
  convert a.sub (b.div_const 64) using 1
  simp only [seg1, coefX, coefY]
  ring

theorem hasDerivAt_seg1 {ε x y h k t : ℝ} (hs : 0 < x + t * h + ε) :
    HasDerivAt (seg1 ε x y h k) (seg2 ε x y h k t) t := by
  have a := hasDerivAt_pw (p := (-1 / 2 : ℝ)) (q := (-3 / 2 : ℝ)) (by norm_num) hs
  have b := hasDerivAt_lin_pw (y := y) (k := k) (p := (-5 / 2 : ℝ)) (q := (-7 / 2 : ℝ))
    (by norm_num) hs
  have c := hasDerivAt_pw (p := (-3 / 2 : ℝ)) (q := (-5 / 2 : ℝ)) (by norm_num) hs
  have e : seg1 ε x y h k = fun u => ((x + u * h + ε) ^ (-1 / 2 : ℝ) / 2 +
      3 * ((y + u * k) * (x + u * h + ε) ^ (-5 / 2 : ℝ)) / 128) * h -
      (x + u * h + ε) ^ (-3 / 2 : ℝ) / 64 * k := by
    funext u; simp only [seg1, coefX, coefY]; ring
  rw [e]
  convert ((((a.div_const 2).add ((b.const_mul 3).div_const 128)).mul_const h).sub
    ((c.div_const 64).mul_const k)) using 1
  simp only [seg2, coefXX, coefXY]
  ring

theorem hasDerivAt_seg2 {ε x y h k t : ℝ} (hs : 0 < x + t * h + ε) :
    HasDerivAt (seg2 ε x y h k) (seg3 ε x y h k t) t := by
  have a := hasDerivAt_pw (p := (-3 / 2 : ℝ)) (q := (-5 / 2 : ℝ)) (by norm_num) hs
  have b := hasDerivAt_lin_pw (y := y) (k := k) (p := (-7 / 2 : ℝ)) (q := (-9 / 2 : ℝ))
    (by norm_num) hs
  have c := hasDerivAt_pw (p := (-5 / 2 : ℝ)) (q := (-7 / 2 : ℝ)) (by norm_num) hs
  have e : seg2 ε x y h k = fun u => 2 * ((-((x + u * h + ε) ^ (-3 / 2 : ℝ) / 8) -
      15 * ((y + u * k) * (x + u * h + ε) ^ (-7 / 2 : ℝ)) / 512) * h ^ 2 +
      3 * (x + u * h + ε) ^ (-5 / 2 : ℝ) / 128 * h * k) := by
    funext u; simp only [seg2, coefXX, coefXY]; ring
  rw [e]
  convert (((((a.div_const 8).neg.sub ((b.const_mul 15).div_const 512)).mul_const (h ^ 2)).add
    ((((c.const_mul 3).div_const 128).mul_const h).mul_const k)).const_mul 2) using 1
  simp only [seg3]
  ring

/-- `s^{-9/2}·s = s^{-7/2}`. -/
theorem rpow_92_mul {s : ℝ} (hs : 0 < s) : s ^ (-9 / 2 : ℝ) * s = s ^ (-7 / 2 : ℝ) := by
  rw [← Real.rpow_add_one hs.ne']; norm_num

/-- The third-derivative bound on the convex region. -/
theorem seg3_le {ε x y h k t : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hy0 : 0 ≤ y + t * k)
    (hyx : y + t * k ≤ x + t * h) :
    seg3 ε x y h k t ≤ ε ^ (-7 / 2 : ℝ) * (|h| ^ 3 + h ^ 2 * |k|) := by
  set s := x + t * h + ε
  have hs : ε ≤ s := by simp only [s]; linarith
  have hs0 : 0 < s := hε.trans_le hs
  set Λ := ε ^ (-7 / 2 : ℝ)
  have hA : s ^ (-5 / 2 : ℝ) ≤ Λ :=
    (Real.rpow_le_rpow_of_nonpos hε hs (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num))
  have hB : s ^ (-7 / 2 : ℝ) ≤ Λ := Real.rpow_le_rpow_of_nonpos hε hs (by norm_num)
  have hC : (y + t * k) * s ^ (-9 / 2 : ℝ) ≤ Λ := by
    have h9 : 0 ≤ s ^ (-9 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
    calc (y + t * k) * s ^ (-9 / 2 : ℝ) ≤ s * s ^ (-9 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (by simp only [s]; linarith) h9
      _ = s ^ (-7 / 2 : ℝ) := by rw [mul_comm, rpow_92_mul hs0]
      _ ≤ Λ := hB
  have hA0 : 0 ≤ s ^ (-5 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hB0 : 0 ≤ s ^ (-7 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hC0 : 0 ≤ (y + t * k) * s ^ (-9 / 2 : ℝ) :=
    mul_nonneg hy0 (Real.rpow_nonneg hs0.le _)
  have hh3 : h ^ 3 ≤ |h| ^ 3 := by rw [← abs_pow]; exact le_abs_self _
  have hh0 : 0 ≤ |h| ^ 3 := by positivity
  have hk : -(h ^ 2 * k) ≤ h ^ 2 * |k| := by
    have := neg_abs_le k
    nlinarith [sq_nonneg h]
  have hhk0 : 0 ≤ h ^ 2 * |k| := by positivity
  have e1 : h ^ 3 * s ^ (-5 / 2 : ℝ) ≤ |h| ^ 3 * Λ :=
    (mul_le_mul_of_nonneg_right hh3 hA0).trans (mul_le_mul_of_nonneg_left hA hh0)
  have e2 : -(h ^ 2 * k) * s ^ (-7 / 2 : ℝ) ≤ h ^ 2 * |k| * Λ :=
    (mul_le_mul_of_nonneg_right hk hB0).trans (mul_le_mul_of_nonneg_left hB hhk0)
  have e3 : h ^ 3 * ((y + t * k) * s ^ (-9 / 2 : ℝ)) ≤ |h| ^ 3 * Λ :=
    (mul_le_mul_of_nonneg_right hh3 hC0).trans (mul_le_mul_of_nonneg_left hC hh0)
  have hΛ0 : 0 ≤ |h| ^ 3 * Λ := mul_nonneg hh0 (Real.rpow_nonneg hε.le _)
  have : seg3 ε x y h k t = 3 / 8 * (h ^ 3 * s ^ (-5 / 2 : ℝ)) +
      45 / 256 * (-(h ^ 2 * k) * s ^ (-7 / 2 : ℝ)) +
      105 / 512 * (h ^ 3 * ((y + t * k) * s ^ (-9 / 2 : ℝ))) := by
    simp only [seg3, s]; ring
  rw [this]
  nlinarith

/-- **The one-step Taylor bound for `Φ_ε` on `0 ≤ y ≤ x`.** -/
theorem lyap_step {ε x y x' y' : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hy' : 0 ≤ y') (hyx' : y' ≤ x') :
    lyap ε x' y' ≤ lyap ε x y + (coefX ε x y * (x' - x) + coefY ε x * (y' - y)) +
      (coefXX ε x y * (x' - x) ^ 2 + coefXY ε x * (x' - x) * (y' - y)) +
      ε ^ (-7 / 2 : ℝ) * (|x' - x| ^ 3 + (x' - x) ^ 2 * |y' - y|) / 6 := by
  set h := x' - x
  set k := y' - y
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ y + t * k ∧ y + t * k ≤ x + t * h := by
    intro t ht
    obtain ⟨t0, t1⟩ := ht
    have e1 : y + t * k = (1 - t) * y + t * y' := by simp only [k]; ring
    have e2 : x + t * h = (1 - t) * x + t * x' := by simp only [h]; ring
    rw [e1, e2]
    constructor
    · have : 0 ≤ 1 - t := by linarith
      positivity
    · have : 0 ≤ 1 - t := by linarith
      nlinarith
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x + t * h + ε := fun t ht => by
    obtain ⟨a, b⟩ := hmem t ht
    linarith
  have hT := taylor2_upper (f := fun u => lyap ε (x + u * h) (y + u * k))
    (fun t ht => hasDerivAt_seg0 (hpos t ht)) (fun t ht => hasDerivAt_seg1 (hpos t ht))
    (fun t ht => hasDerivAt_seg2 (hpos t ht))
    (fun t ht => seg3_le hε hε1 (hmem t ht).1 (hmem t ht).2)
  have ex : x + 1 * h = x' := by simp only [h]; ring
  have ey : y + 1 * k = y' := by simp only [k]; ring
  simp only [ex, ey, zero_mul, add_zero, seg1, seg2] at hT
  linarith

end BlockBand.Transmission.LawDecay
