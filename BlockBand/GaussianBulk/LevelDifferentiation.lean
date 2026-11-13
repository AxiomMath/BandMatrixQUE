module

public import Mathlib
public import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
public import BlockBand.GaussianBulk.LevelGraph

/-!
# Derivatives of the level graph

For a finite real source `d`, `N > 0` and `t > 0`, the level height `y(x)` is differentiable
wherever it is positive, with `y' = -A₁/(yB)` by the implicit function theorem. The horizontal
coordinate `ψ(x) = x + t N⁻¹ Σ_j (x - d_j)/((x - d_j)² + y²)` has derivative
`ψ' = 2t(y²B + A₁²/B) ≥ 2y²/t`, and the slope satisfies `|y'| ≤ √t/y`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open scoped BigOperators

/-- The fourth inverse-distance moment `B = N⁻¹ Σ_j ((x - d_j)² + y²)⁻²`. -/
def levelB {N : ℕ} (d : Fin N → ℝ) (x y : ℝ) : ℝ :=
  realMean (fun j => (((x-d j)^2+y^2)⁻¹)^2)

/-- The weighted fourth inverse-distance moment `A₁ = N⁻¹ Σ_j (x - d_j)((x - d_j)² + y²)⁻²`. -/
def levelA1 {N : ℕ} (d : Fin N → ℝ) (x y : ℝ) : ℝ :=
  realMean (fun j => (x-d j)*(((x-d j)^2+y^2)⁻¹)^2)

/-- Multiplication by a real scalar as a continuous linear map. -/
def scalarCLM (c : ℝ) : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ

/-- Multiplication by a nonzero scalar is invertible. -/
theorem scalarCLM_isInvertible (c : ℝ) (hc : c ≠ 0) : (scalarCLM c).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := scalarCLM c⁻¹)
  all_goals simp [scalarCLM,hc]

/-- The inverse of multiplication by a nonzero scalar. -/
theorem scalarCLM_inverse (c : ℝ) (hc : c ≠ 0) :
    (scalarCLM c).inverse = scalarCLM c⁻¹ := by
  apply ContinuousLinearMap.inverse_eq
  all_goals simp [scalarCLM,hc]

/-- The vertical partial derivative of the level: `∂_y level = -2yB`. -/
theorem hasDerivAt_verticalLevel_y {N : ℕ} (d : Fin N → ℝ)
    (x y : ℝ) (hy : 0 < y) :
    HasDerivAt (verticalLevel d x) (-2*y*levelB d x y) y := by
  have ht (j : Fin N) : HasDerivAt (fun w : ℝ => ((x-d j)^2+w^2)⁻¹)
      (-2*y*(((x-d j)^2+y^2)⁻¹)^2) y := by
    have h := ((hasDerivAt_const y ((x-d j)^2)).add
      ((hasDerivAt_id y).pow 2)).inv (ne_of_gt (level_denominator_pos (x-d j) y hy))
    have h' : HasDerivAt (fun w : ℝ => ((x-d j)^2+w^2)⁻¹)
        (-(2*y)/((x-d j)^2+y^2)^2) y := by
      convert! h using 1
      all_goals first | rfl | (funext w) | simp
    apply h'.congr_deriv
    simp only [div_eq_mul_inv,inv_pow]
    ring
  have hs := (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht j)).const_mul (N : ℝ)⁻¹
  apply hs.congr_deriv
  unfold levelB realMean
  rw [← Finset.mul_sum]
  ring

/-- The horizontal partial derivative of the level: `∂_x level = -2A₁`. -/
theorem hasDerivAt_verticalLevel_x {N : ℕ} (d : Fin N → ℝ)
    (x y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun a => verticalLevel d a y) (-2*levelA1 d x y) x := by
  have ht (j : Fin N) : HasDerivAt (fun a : ℝ => ((a-d j)^2+y^2)⁻¹)
      (-2*((x-d j)*(((x-d j)^2+y^2)⁻¹)^2)) x := by
    have h := ((((hasDerivAt_id x).sub_const (d j)).pow 2).add_const (y^2)).inv
      (ne_of_gt (level_denominator_pos (x-d j) y hy))
    have h' : HasDerivAt (fun a : ℝ => ((a-d j)^2+y^2)⁻¹)
        (-(2*(x-d j))/((x-d j)^2+y^2)^2) x := by
      convert! h using 1
      all_goals first | rfl | (funext w) | simp
    apply h'.congr_deriv
    simp only [div_eq_mul_inv,inv_pow]
    ring
  have hs := (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht j)).const_mul (N : ℝ)⁻¹
  apply hs.congr_deriv
  unfold levelA1 realMean
  rw [← Finset.mul_sum]
  ring

/-- Positive height makes `B` strictly positive. -/
theorem levelB_pos {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (x y : ℝ) (hy : 0 < y) : 0 < levelB d x y := by
  unfold levelB realMean
  apply mul_pos (inv_pos.mpr (by exact_mod_cast hN))
  apply Finset.sum_pos
  · intro j _
    exact sq_pos_of_pos (inv_pos.mpr (level_denominator_pos (x-d j) y hy))
  · exact ⟨⟨0,hN⟩,Finset.mem_univ _⟩

/-- `B` is continuous at every point of the upper half-plane. -/
theorem levelB_continuousAt {N : ℕ} (d : Fin N → ℝ)
    (u : ℝ × ℝ) (hu : 0 < u.2) : ContinuousAt (fun p => levelB d p.1 p.2) u := by
  unfold levelB realMean
  apply continuousAt_const.mul
  apply tendsto_finsetSum
  intro j _
  have hden : ContinuousAt (fun p : ℝ × ℝ => (p.1-d j)^2+p.2^2) u := by fun_prop
  exact (hden.inv₀ (ne_of_gt (level_denominator_pos (u.1-d j) u.2 hu))).pow 2

/-- `A₁` is continuous at every point of the upper half-plane. -/
theorem levelA1_continuousAt {N : ℕ} (d : Fin N → ℝ)
    (u : ℝ × ℝ) (hu : 0 < u.2) : ContinuousAt (fun p => levelA1 d p.1 p.2) u := by
  unfold levelA1 realMean
  apply continuousAt_const.mul
  apply tendsto_finsetSum
  intro j _
  have hden : ContinuousAt (fun p : ℝ × ℝ => (p.1-d j)^2+p.2^2) u := by fun_prop
  exact (continuousAt_fst.sub continuousAt_const).mul
    ((hden.inv₀ (ne_of_gt (level_denominator_pos (u.1-d j) u.2 hu))).pow 2)

/-- The horizontal partial derivative as a continuous linear map. -/
def levelPartialX {N : ℕ} (d : Fin N → ℝ) (x y : ℝ) : ℝ →L[ℝ] ℝ :=
  scalarCLM (-2*levelA1 d x y)

/-- The vertical partial derivative as a continuous linear map. -/
def levelPartialY {N : ℕ} (d : Fin N → ℝ) (x y : ℝ) : ℝ →L[ℝ] ℝ :=
  scalarCLM (-2*y*levelB d x y)

/-- The horizontal Fréchet partial derivative of the level. -/
theorem hasFDerivAt_verticalLevel_x {N : ℕ} (d : Fin N → ℝ)
    (x y : ℝ) (hy : 0 < y) :
    HasFDerivAt (fun a => verticalLevel d a y) (levelPartialX d x y) x := by
  convert! (hasDerivAt_verticalLevel_x d x y hy).hasFDerivAt using 1
  ext
  simp [levelPartialX,scalarCLM]

/-- The vertical Fréchet partial derivative of the level. -/
theorem hasFDerivAt_verticalLevel_y {N : ℕ} (d : Fin N → ℝ)
    (x y : ℝ) (hy : 0 < y) :
    HasFDerivAt (verticalLevel d x) (levelPartialY d x y) y := by
  convert! (hasDerivAt_verticalLevel_y d x y hy).hasFDerivAt using 1
  ext
  simp [levelPartialY,scalarCLM]

/-- The level height is differentiable at every active point, with `y' = -A₁/(yB)`. -/
theorem hasDerivAt_levelHeight {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) (hx : LevelActive d t x) :
    HasDerivAt (levelHeight d t)
      (-levelA1 d x (levelHeight d t x) /
        (levelHeight d t x*levelB d x (levelHeight d t x))) x := by
  let y := levelHeight d t x
  have hr : PositiveLevelRoot d t x y := levelHeight_root hN d t x ht hx
  have hb := levelB_pos hN d x y hr.1
  have hc : -2*y*levelB d x y ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hr.1)) (ne_of_gt hb)
  have hn : ∀ᶠ u : ℝ × ℝ in nhds (x,y), 0 < u.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hr.1
  have df1 : ∀ᶠ u : ℝ × ℝ in nhds (x,y),
      HasFDerivAt (fun a => verticalLevel d a u.2) (levelPartialX d u.1 u.2) u.1 := by
    filter_upwards [hn] with u hu
    exact hasFDerivAt_verticalLevel_x d u.1 u.2 hu
  have df2 : ∀ᶠ u : ℝ × ℝ in nhds (x,y),
      HasFDerivAt (verticalLevel d u.1) (levelPartialY d u.1 u.2) u.2 := by
    filter_upwards [hn] with u hu
    exact hasFDerivAt_verticalLevel_y d u.1 u.2 hu
  have cf1 : ContinuousAt (fun u : ℝ × ℝ => levelPartialX d u.1 u.2) (x,y) := by
    exact (continuousAt_const.mul (levelA1_continuousAt d (x,y) hr.1)).smul continuousAt_const
  have cf2 : ContinuousAt (fun u : ℝ × ℝ => levelPartialY d u.1 u.2) (x,y) := by
    exact ((continuousAt_const.mul continuousAt_snd).mul
      (levelB_continuousAt d (x,y) hr.1)).smul continuousAt_const
  have hi : (levelPartialY d x y).IsInvertible := scalarCLM_isInvertible _ hc
  let ψ := implicitFunctionOfBivariate df1 df2 cf1 cf2 hi
  have hp : HasDerivAt ψ
      ((-(levelPartialY d x y).inverse ∘L levelPartialX d x y) 1) x :=
    (hasStrictFDerivAt_implicitFunctionOfBivariate df1 df2 cf1 cf2 hi).hasFDerivAt.hasDerivAt
  have he : ∀ᶠ a in nhds x, verticalLevel d a (ψ a) = 1/t := by
    have h := eventually_apply_implicitFunctionOfBivariate df1 df2 cf1 cf2 hi
    simpa only [hr.2] using h
  have hpos : ∀ᶠ a in nhds x, 0 < ψ a :=
    (tendsto_implicitFunctionOfBivariate df1 df2 cf1 cf2 hi)
      ((isOpen_Ioi.mem_nhds hr.1))
  have heq : levelHeight d t =ᶠ[nhds x] ψ := by
    filter_upwards [he,hpos] with a ha hpa
    exact levelHeight_eq_of_root hN d t a (ψ a) ht ⟨hpa,ha⟩
  have hgraph := hp.congr_of_eventuallyEq heq
  apply hgraph.congr_deriv
  dsimp only [levelPartialY,levelPartialX]
  rw [scalarCLM_inverse _ hc]
  simp only [ContinuousLinearMap.comp_apply,neg_apply,
    scalarCLM,smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul,mul_one]
  change -((-2*y*levelB d x y)⁻¹*(-2*levelA1 d x y)) =
    -levelA1 d x y/(y*levelB d x y)
  field_simp [ne_of_gt hr.1,ne_of_gt hb]

/-- Jensen's lower bound `B ≥ 1/t²` at a positive level root. -/
theorem levelB_ge_inv_sq {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x y : ℝ) (hy : PositiveLevelRoot d t x y) : 1/t^2 ≤ levelB d x y := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have he : (∑ j, ((x-d j)^2+y^2)⁻¹)/(Fintype.card (Fin N) : ℝ) = 1/t := by
    simpa [verticalLevel,realMean,div_eq_mul_inv,mul_comm] using hy.2
  have h := fourth_moment_lower_of_level (fun j : Fin N => ((x-d j)^2+y^2)⁻¹) t he
  simpa [levelB,realMean,div_eq_mul_inv,mul_comm] using h

/-- The horizontal coordinate `ψ(x) = x + t N⁻¹ Σ_j (x - d_j)/((x - d_j)² + y(x)²)`. -/
def levelPsi {N : ℕ} (d : Fin N → ℝ) (t x : ℝ) : ℝ :=
  x+t*realMean (fun j => (x-d j)/((x-d j)^2+(levelHeight d t x)^2))

/-- Coefficient algebra for the quotient rule in the derivative of `ψ`. -/
private theorem mean_psi_coefficient {N : ℕ} (d : Fin N → ℝ)
    (x y γ : ℝ) (hy : 0 < y) :
    realMean (fun j => (y^2-(x-d j)^2-2*y*γ*(x-d j))*(((x-d j)^2+y^2)⁻¹)^2) =
      2*y^2*levelB d x y-verticalLevel d x y-2*y*γ*levelA1 d x y := by
  have hterm (j : Fin N) :
      (y^2-(x-d j)^2-2*y*γ*(x-d j))*(((x-d j)^2+y^2)⁻¹)^2 =
      2*y^2*(((x-d j)^2+y^2)⁻¹)^2-((x-d j)^2+y^2)⁻¹-
        2*y*γ*((x-d j)*(((x-d j)^2+y^2)⁻¹)^2) := by
    field_simp [ne_of_gt (level_denominator_pos (x-d j) y hy)]; ring
  calc
    _ = realMean (fun j => 2*y^2*(((x-d j)^2+y^2)⁻¹)^2-
        ((x-d j)^2+y^2)⁻¹-2*y*γ*((x-d j)*(((x-d j)^2+y^2)⁻¹)^2)) := by
      congr 1
      funext j
      exact hterm j
    _ = _ := by
      unfold realMean levelB verticalLevel levelA1 realMean
      simp only [Finset.sum_sub_distrib,mul_sub,Finset.mul_sum]
      ring

/-- The derivative of the horizontal coordinate at every active point:
`ψ' = 2t(y²B + A₁²/B)`. -/
theorem hasDerivAt_levelPsi {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) (hx : LevelActive d t x) :
    HasDerivAt (levelPsi d t)
      (2*t*((levelHeight d t x)^2*levelB d x (levelHeight d t x)+
        (levelA1 d x (levelHeight d t x))^2/levelB d x (levelHeight d t x))) x := by
  let y := levelHeight d t x
  let γ := -levelA1 d x y/(y*levelB d x y)
  have hr : PositiveLevelRoot d t x y := levelHeight_root hN d t x ht hx
  have hb := levelB_pos hN d x y hr.1
  have hY : HasDerivAt (levelHeight d t) γ x := hasDerivAt_levelHeight hN d t x ht hx
  have hterm (j : Fin N) :
      HasDerivAt (fun a => (a-d j)/((a-d j)^2+(levelHeight d t a)^2))
        ((y^2-(x-d j)^2-2*y*γ*(x-d j))*(((x-d j)^2+y^2)⁻¹)^2) x := by
    have hX := (hasDerivAt_id x).sub_const (d j)
    have hden := (hX.pow 2).add (hY.pow 2)
    have hquot := hX.div hden (ne_of_gt (level_denominator_pos (x-d j) y hr.1))
    have hq : HasDerivAt (fun a => (a-d j)/((a-d j)^2+(levelHeight d t a)^2))
        (((x-d j)^2+y^2-(x-d j)*(2*(x-d j)+2*y*γ))/((x-d j)^2+y^2)^2) x := by
      convert! hquot using 1
      all_goals first | rfl | (funext a) | (simp [y])
    apply hq.congr_deriv
    simp only [div_eq_mul_inv,inv_pow]
    ring
  have hs := ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j)).const_mul
    (N : ℝ)⁻¹).const_mul t
  have hp := (hasDerivAt_id x).add hs
  apply hp.congr_deriv
  change 1+t*realMean (fun j =>
      (y^2-(x-d j)^2-2*y*γ*(x-d j))*(((x-d j)^2+y^2)⁻¹)^2) = _
  rw [mean_psi_coefficient d x y γ hr.1,hr.2]
  change 1+t*(2*y^2*levelB d x y-1/t-2*y*
      (-levelA1 d x y/(y*levelB d x y))*levelA1 d x y) =
    2*t*(y^2*levelB d x y+(levelA1 d x y)^2/levelB d x y)
  field_simp [ne_of_gt ht,ne_of_gt hr.1,ne_of_gt hb]; ring

/-- The lower bound `ψ' ≥ 2y²/t` at every active point. -/
theorem deriv_levelPsi_lower {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) (hx : LevelActive d t x) :
    2*(levelHeight d t x)^2/t ≤ deriv (levelPsi d t) x := by
  have hr := levelHeight_root hN d t x ht hx
  rw [(hasDerivAt_levelPsi hN d t x ht hx).deriv]
  exact horizontal_curvature_lower t _ _ _ ht
    (levelB_pos hN d x _ hr.1) (levelB_ge_inv_sq hN d t x _ hr)

/-- The derivative of `ψ` is strictly positive at every active point. -/
theorem deriv_levelPsi_pos {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) (hx : LevelActive d t x) : 0 < deriv (levelPsi d t) x := by
  have hy := (levelHeight_root hN d t x ht hx).1
  exact lt_of_lt_of_le (div_pos (mul_pos (by norm_num) (sq_pos_of_pos hy)) ht)
    (deriv_levelPsi_lower hN d t x ht hx)

/-- Cauchy–Schwarz: `A₁² ≤ level · B`. -/
theorem levelA1_sq_le_level_mul_levelB {N : ℕ} (d : Fin N → ℝ)
    (x y : ℝ) (hy : 0 < y) :
    (levelA1 d x y)^2 ≤ verticalLevel d x y*levelB d x y := by
  let r : Fin N → ℝ := fun j => ((x-d j)^2+y^2)⁻¹
  have hs : (∑ j, ((x-d j)*r j)*r j) = ∑ j, (x-d j)*(r j)^2 := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin N => (x-d j)*r j) r
  rw [hs] at hcs
  have hnorm : (levelA1 d x y)^2 ≤
      realMean (fun j => ((x-d j)*r j)^2)*levelB d x y := by
    have h := mul_le_mul_of_nonneg_left hcs (sq_nonneg (N : ℝ)⁻¹)
    convert! h using 1
    all_goals
      try unfold levelA1
      try unfold levelB
      unfold realMean
      dsimp only [r]
      ring
  have hterm (j : Fin N) : ((x-d j)*r j)^2 ≤ r j := by
    have hden := ne_of_gt (level_denominator_pos (x-d j) y hy)
    have hid : ((x-d j)^2+y^2)*(r j)^2 = r j := by
      dsimp only [r]
      field_simp [hden]
    nlinarith [sq_nonneg (y*r j)]
  have hb : 0 ≤ levelB d x y := by
    unfold levelB realMean
    positivity
  have hm : realMean (fun j => ((x-d j)*r j)^2) ≤ verticalLevel d x y := by
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hterm j)) (by positivity)
  exact le_trans hnorm (mul_le_mul_of_nonneg_right hm hb)

/-- The slope bound `|y'| ≤ √t/y` at every active point. -/
theorem abs_deriv_levelHeight_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) (hx : LevelActive d t x) :
    |deriv (levelHeight d t) x| ≤ Real.sqrt t/levelHeight d t x := by
  let y := levelHeight d t x
  let B := levelB d x y
  let A := levelA1 d x y
  have hr : PositiveLevelRoot d t x y := levelHeight_root hN d t x ht hx
  have hb : 0 < B := levelB_pos hN d x y hr.1
  have hJ : 1/t^2 ≤ B := levelB_ge_inv_sq hN d t x y hr
  have hcs : A^2 ≤ (1/t)*B := by
    simpa only [hr.2] using levelA1_sq_le_level_mul_levelB d x y hr.1
  have hq : A^2 ≤ t*B^2 := by
    apply le_trans hcs
    have hh := mul_le_mul_of_nonneg_left hJ
      (show 0 ≤ t*B from mul_nonneg (le_of_lt ht) (le_of_lt hb))
    have heq : t*B*(1/t^2) = (1/t)*B := by field_simp [ne_of_gt ht]
    rw [heq] at hh
    nlinarith
  have habs : |A| ≤ Real.sqrt t*B := by
    have he : (Real.sqrt t*B)^2 = t*B^2 := by rw [mul_pow,Real.sq_sqrt (le_of_lt ht)]
    have hnonneg : 0 ≤ Real.sqrt t*B := mul_nonneg (Real.sqrt_nonneg t) (le_of_lt hb)
    nlinarith [sq_abs A,abs_nonneg A]
  rw [(hasDerivAt_levelHeight hN d t x ht hx).deriv]
  change |-A/(y*B)| ≤ Real.sqrt t/y
  rw [abs_div,abs_neg,abs_of_pos (mul_pos hr.1 hb)]
  apply (div_le_iff₀ (mul_pos hr.1 hb)).mpr
  have heq : (Real.sqrt t/y)*(y*B) = Real.sqrt t*B := by
    field_simp [ne_of_gt hr.1]
  rw [heq]
  exact habs

/-- Uniform slope bound on any strip `y ≥ η`, for `t ≤ tmax`, independent of `N` and `d`. -/
theorem abs_deriv_levelHeight_uniform {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x η tmax : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (hη : 0 < η) (hheight : η ≤ levelHeight d t x) :
    |deriv (levelHeight d t) x| ≤ Real.sqrt tmax/η := by
  have hx := (levelHeight_pos_iff hN d t x ht).mp (lt_of_lt_of_le hη hheight)
  calc
    _ ≤ Real.sqrt t/levelHeight d t x := abs_deriv_levelHeight_le hN d t x ht hx
    _ ≤ Real.sqrt t/η := div_le_div_of_nonneg_left (Real.sqrt_nonneg t) hη hheight
    _ ≤ Real.sqrt tmax/η := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt htmax) (le_of_lt hη)

end BlockBand.GaussianBulk
