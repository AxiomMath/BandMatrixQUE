module

public import BlockBand.Diffusion.Kernel.McKeanPDEJoint

/-!
# Angular calculus of the hyperbolic law of cosines

For `x > 0`, `x' ≥ 0` write `α = √(x(1+x))`, `β = √(x'(1+x'))`, `a = 1+2x`, `b = 1+2x'`, so
that `C = mkHypCos x x' θ = ab - 4αβ cos θ` (`mk_hypCos_eq_mul`). We record its partial
derivatives:
* `∂_x C = mkCx x x' θ = 2b - 4β cos θ · a/(2α)` (`mk_hasDerivAt_hypCos_x`);
* `∂_x² C = mkCxx x x' θ = -4β cos θ · (4α - a²/α)/(4α²)` (`mk_hasDerivAt_cx`);
* `∂_θ C = mkCth x x' θ = 4√(x(1+x)x'(1+x')) sin θ`, `∂_θ² C = mkCthth x x' θ`
  (`… cos θ`), valid for all real arguments;
and prove the two angular identities (in the variable `x`, `a = 1 + 2x`):
* `mk_angular_one`: `x(1+x) (∂_x C)² + (∂_θ C)²/(4x(1+x)) = C² - 1`;
* `mk_angular_two`: `x(1+x) ∂_x² C + (1+2x) ∂_x C + ∂_θ² C/(4x(1+x)) = 2C`;
hence the pointwise identity `mk_angular_pde`: for all reals `k₁, k₂`,
`x(1+x)(k₂ C_x² + k₁ C_xx) + (1+2x) k₁ C_x = (C²-1) k₂ + 2C k₁ - (k₂ C_θ² + k₁ C_θθ)/(4x(1+x))`.
Finally `mk_one_lt_hypCos`: off the diagonal (`x, x' ≥ 0`, `x ≠ x'`) one has `C > 1` for every `θ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real

/-- `∂_x mkHypCos` for `x > 0`. -/
def mkCx (x x' θ : ℝ) : ℝ :=
  2 * (1 + 2 * x') -
    4 * Real.sqrt (x' * (1 + x')) * Real.cos θ * ((1 + 2 * x) / (2 * Real.sqrt (x * (1 + x))))

/-- `∂_x² mkHypCos` for `x > 0`. -/
def mkCxx (x x' θ : ℝ) : ℝ :=
  -(4 * Real.sqrt (x' * (1 + x')) * Real.cos θ) *
    ((4 * Real.sqrt (x * (1 + x)) - (1 + 2 * x) ^ 2 / Real.sqrt (x * (1 + x))) /
      (4 * Real.sqrt (x * (1 + x)) ^ 2))

/-- `∂_θ mkHypCos`. -/
def mkCth (x x' θ : ℝ) : ℝ := 4 * Real.sqrt (x * (1 + x) * (x' * (1 + x'))) * Real.sin θ

/-- `∂_θ² mkHypCos`. -/
def mkCthth (x x' θ : ℝ) : ℝ := 4 * Real.sqrt (x * (1 + x) * (x' * (1 + x'))) * Real.cos θ

theorem mk_hypCos_eq_mul {x : ℝ} (hx : 0 ≤ x) (x' θ : ℝ) :
    mkHypCos x x' θ = (1 + 2 * x) * (1 + 2 * x') -
      4 * Real.sqrt (x * (1 + x)) * Real.sqrt (x' * (1 + x')) * Real.cos θ := by
  rw [mkHypCos, Real.sqrt_mul (by positivity)]; ring

theorem mk_al_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sqrt (x * (1 + x)) :=
  Real.sqrt_pos.2 (by positivity)

theorem mk_hasDerivAt_al {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => Real.sqrt (z * (1 + z)))
      ((1 + 2 * x) / (2 * Real.sqrt (x * (1 + x)))) x := by
  have hp : HasDerivAt (fun z : ℝ => z * (1 + z)) (1 + 2 * x) x := by
    have := (hasDerivAt_id x).mul ((hasDerivAt_id x).const_add 1)
    convert this using 1
    · funext z; simp only [Pi.mul_apply, id]
    · simp only [id]; ring
  have h := hp.sqrt (by positivity)
  convert h using 1

theorem mk_hasDerivAt_hypCos_x {x : ℝ} (hx : 0 < x) (x' θ : ℝ) :
    HasDerivAt (fun z => mkHypCos z x' θ) (mkCx x x' θ) x := by
  have heq : (fun z => mkHypCos z x' θ) =ᶠ[𝓝 x] fun z => (1 + 2 * z) * (1 + 2 * x') -
      4 * Real.sqrt (x' * (1 + x')) * Real.cos θ * Real.sqrt (z * (1 + z)) := by
    filter_upwards [lt_mem_nhds hx] with z hz
    rw [mk_hypCos_eq_mul hz.le]; ring
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have h := ((((hasDerivAt_id x).const_mul 2).const_add 1).mul_const (1 + 2 * x')).sub
    ((mk_hasDerivAt_al hx).const_mul (4 * Real.sqrt (x' * (1 + x')) * Real.cos θ))
  convert h using 1
  · rfl
  · unfold mkCx; ring

theorem mk_hasDerivAt_cx {x : ℝ} (hx : 0 < x) (x' θ : ℝ) :
    HasDerivAt (fun z => mkCx z x' θ) (mkCxx x x' θ) x := by
  have hα := (mk_al_pos hx).ne'
  have hq := (((hasDerivAt_id x).const_mul 2).const_add 1).div
    ((mk_hasDerivAt_al hx).const_mul 2) (by positivity)
  have h := (hq.const_mul (4 * Real.sqrt (x' * (1 + x')) * Real.cos θ)).const_sub
    (2 * (1 + 2 * x'))
  unfold mkCx
  convert h using 1
  · funext z; simp only [Pi.div_apply, id]
  · unfold mkCxx; simp only [id]
    field_simp
    ring

theorem mk_hasDerivAt_hypCos_θ (x x' θ : ℝ) :
    HasDerivAt (fun φ => mkHypCos x x' φ) (mkCth x x' θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).const_mul
    (4 * Real.sqrt (x * (1 + x) * (x' * (1 + x'))))).const_sub ((1 + 2 * x) * (1 + 2 * x'))
  unfold mkHypCos mkCth
  convert h using 1
  ring

theorem mk_hasDerivAt_cth (x x' θ : ℝ) :
    HasDerivAt (fun φ => mkCth x x' φ) (mkCthth x x' θ) θ := by
  have h := (Real.hasDerivAt_sin θ).const_mul (4 * Real.sqrt (x * (1 + x) * (x' * (1 + x'))))
  unfold mkCth mkCthth
  exact h

theorem mk_cth_zero (x x' : ℝ) : mkCth x x' 0 = 0 := by simp [mkCth]

theorem mk_cth_two_pi (x x' : ℝ) : mkCth x x' (2 * π) = 0 := by simp [mkCth]

/-- **First angular identity.** `x(1+x) C_x² + C_θ²/(4x(1+x)) = C² - 1` for `x > 0`,
`x' ≥ 0`. -/
theorem mk_angular_one {x x' : ℝ} (hx : 0 < x) (hx' : 0 ≤ x') (θ : ℝ) :
    x * (1 + x) * mkCx x x' θ ^ 2 + mkCth x x' θ ^ 2 / (4 * (x * (1 + x))) =
      mkHypCos x x' θ ^ 2 - 1 := by
  have hα0 := (mk_al_pos hx).ne'
  have hαsq : Real.sqrt (x * (1 + x)) ^ 2 = x * (1 + x) := Real.sq_sqrt (by positivity)
  have hβsq : Real.sqrt (x' * (1 + x')) ^ 2 = x' * (1 + x') := Real.sq_sqrt (by positivity)
  have hsc := Real.sin_sq_add_cos_sq θ
  rw [mk_hypCos_eq_mul hx.le]
  unfold mkCx mkCth
  rw [Real.sqrt_mul (show 0 ≤ x * (1 + x) by positivity) (x' * (1 + x'))]
  set α := Real.sqrt (x * (1 + x))
  set β := Real.sqrt (x' * (1 + x'))
  rw [← hαsq]
  have r1 : α ^ 2 * (2 * (1 + 2 * x') - 4 * β * Real.cos θ * ((1 + 2 * x) / (2 * α))) ^ 2 +
      (4 * (α * β) * Real.sin θ) ^ 2 / (4 * α ^ 2) =
      (2 * (1 + 2 * x') * α - 2 * β * (1 + 2 * x) * Real.cos θ) ^ 2 +
        4 * β ^ 2 * Real.sin θ ^ 2 := by
    field_simp; ring
  rw [r1]
  linear_combination (-4) * (4 * α ^ 2 - (1 + 2 * x) ^ 2) * hβsq +
    (-4) * (4 * β ^ 2 * Real.cos θ ^ 2 - (1 + 4 * β ^ 2)) * hαsq + 4 * β ^ 2 * hsc

/-- **Second angular identity.** `x(1+x) C_xx + (1+2x) C_x + C_θθ/(4x(1+x)) = 2C` for `x > 0`
(any `x'`). -/
theorem mk_angular_two {x : ℝ} (hx : 0 < x) (x' θ : ℝ) :
    x * (1 + x) * mkCxx x x' θ + (1 + 2 * x) * mkCx x x' θ +
      mkCthth x x' θ / (4 * (x * (1 + x))) = 2 * mkHypCos x x' θ := by
  have hα0 := (mk_al_pos hx).ne'
  have hαsq : Real.sqrt (x * (1 + x)) ^ 2 = x * (1 + x) := Real.sq_sqrt (by positivity)
  rw [mk_hypCos_eq_mul hx.le]
  unfold mkCx mkCxx mkCthth
  rw [Real.sqrt_mul (show 0 ≤ x * (1 + x) by positivity) (x' * (1 + x'))]
  set α := Real.sqrt (x * (1 + x))
  set β := Real.sqrt (x' * (1 + x'))
  rw [← hαsq]
  have r1 : α ^ 2 * (-(4 * β * Real.cos θ) * ((4 * α - (1 + 2 * x) ^ 2 / α) / (4 * α ^ 2))) +
      (1 + 2 * x) * (2 * (1 + 2 * x') - 4 * β * Real.cos θ * ((1 + 2 * x) / (2 * α))) +
      4 * (α * β) * Real.cos θ / (4 * α ^ 2) -
      2 * ((1 + 2 * x) * (1 + 2 * x') - 4 * α * β * Real.cos θ) =
      β * Real.cos θ / α * (1 - (1 + 2 * x) ^ 2 + 4 * α ^ 2) := by
    field_simp; ring
  have r2 : 1 - (1 + 2 * x) ^ 2 + 4 * α ^ 2 = 0 := by rw [hαsq]; ring
  rw [r2, mul_zero] at r1
  linarith

/-- **The pointwise angular PDE identity.** For `x > 0`, `x' ≥ 0` and all reals `k₁, k₂`
(to be `∂_c K`, `∂_c² K` at `c = C`):
`x(1+x)(k₂ C_x² + k₁ C_xx) + (1+2x) k₁ C_x = (C²-1) k₂ + 2C k₁ - (k₂ C_θ² + k₁ C_θθ)/(4x(1+x))`. -/
theorem mk_angular_pde {x x' : ℝ} (hx : 0 < x) (hx' : 0 ≤ x') (θ k₁ k₂ : ℝ) :
    x * (1 + x) * (k₂ * mkCx x x' θ ^ 2 + k₁ * mkCxx x x' θ) + (1 + 2 * x) * (k₁ * mkCx x x' θ) =
      (mkHypCos x x' θ ^ 2 - 1) * k₂ + 2 * mkHypCos x x' θ * k₁ -
        (k₂ * mkCth x x' θ ^ 2 + k₁ * mkCthth x x' θ) / (4 * (x * (1 + x))) := by
  have e1 := mk_angular_one hx hx' θ
  have e2 := mk_angular_two hx x' θ
  have hx0 : 4 * (x * (1 + x)) ≠ 0 := by positivity
  rw [← e1, ← e2]
  field_simp
  ring

/-- Off the diagonal, `cosh d > 1` for every angle. -/
theorem mk_one_lt_hypCos {x x' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (hne : x ≠ x') (θ : ℝ) :
    1 < mkHypCos x x' θ := by
  obtain ⟨h1, h2⟩ := mk_hypCos_sub_one hx hx' θ
  have hpos : 0 < ((1 + 2 * x) - (1 + 2 * x')) ^ 2 := by
    have : (1 + 2 * x) - (1 + 2 * x') ≠ 0 := by
      intro h; exact hne (by linarith)
    positivity
  have hab : 0 < 2 * (1 + 2 * x) * (1 + 2 * x') := by positivity
  by_contra hle
  push Not at hle
  have : mkHypCos x x' θ - 1 ≤ 0 := by linarith
  nlinarith

end BlockBand.Diffusion
