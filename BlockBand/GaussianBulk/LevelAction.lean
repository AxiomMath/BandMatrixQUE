module

public import BlockBand.GaussianBulk.LevelDifferentiation

/-!
# The action along the level graph

Along the upper level graph `x ↦ x + i y(x)`, the horizontal coordinate `ψ` (`levelPsi`) is
continuous and strictly increasing with `|ψ(x) - x| ≤ √t`, and the real part of the Johansson
saddle phase (`levelAction`) is continuous with derivative `(ψ - E)/t`. At a solution of the
finite MDE, the real part of the saddle point is the unique point with `ψ = E`.
-/

set_option autoImplicit false
@[expose] public section
namespace BlockBand.GaussianBulk

open Filter Topology
noncomputable section

/-- Every squared distance `(x - d_j)² + y(x)²` on the graph is strictly positive. -/
theorem levelGraph_denominator_pos {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) (j : Fin N) :
    0 < (x-d j)^2+(levelHeight d t x)^2 := by
  by_cases hx : x=d j
  · subst x
    exact level_denominator_pos _ _ (levelHeight_at_pole_pos hN d t ht j)
  · have ha : 0 < (x-d j)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
    exact add_pos_of_pos_of_nonneg ha (sq_nonneg _)

/-- The horizontal coordinate `ψ` is continuous on `ℝ`. -/
theorem levelPsi_continuous {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t : ℝ) (ht : 0 < t) : Continuous (levelPsi d t) := by
  have hY := levelHeight_continuous hN d t ht
  have hterm (j : Fin N) : Continuous (fun x =>
      (x-d j)/((x-d j)^2+(levelHeight d t x)^2)) :=
    (continuous_id.sub continuous_const).div
      (((continuous_id.sub continuous_const).pow 2).add (hY.pow 2))
      (fun x => ne_of_gt (levelGraph_denominator_pos hN d t x ht j))
  exact continuous_id.add (continuous_const.mul (continuous_const.mul
    (continuous_finsetSum Finset.univ (fun j _ => hterm j))))

/-- The real part of the Johansson saddle phase along the upper level graph, written with
logarithms of squared distances. -/
def levelAction {N : ℕ} (d : Fin N → ℝ) (E t x : ℝ) : ℝ :=
  ((x-E)^2-(levelHeight d t x)^2)/(2*t)+
    realMean (fun j => Real.log ((x-d j)^2+(levelHeight d t x)^2))/2

/-- The level action is continuous on `ℝ`. -/
theorem levelAction_continuous {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t : ℝ) (ht : 0 < t) : Continuous (levelAction d E t) := by
  have hY := levelHeight_continuous hN d t ht
  have hterm (j : Fin N) : Continuous (fun x =>
      Real.log ((x-d j)^2+(levelHeight d t x)^2)) :=
    (((continuous_id.sub continuous_const).pow 2).add (hY.pow 2)).log
      (fun x => ne_of_gt (levelGraph_denominator_pos hN d t x ht j))
  exact ((((continuous_id.sub continuous_const).pow 2).sub (hY.pow 2)).div_const _).add
    ((continuous_const.mul (continuous_finsetSum Finset.univ
      (fun j _ => hterm j))).div_const _)

/-- At every active point the level action has derivative `(ψ - E)/t`. -/
theorem hasDerivAt_levelAction {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x : ℝ) (ht : 0 < t) (hx : LevelActive d t x) :
    HasDerivAt (levelAction d E t) ((levelPsi d t x-E)/t) x := by
  let y := levelHeight d t x
  let γ := -levelA1 d x y/(y*levelB d x y)
  have hr : PositiveLevelRoot d t x y := levelHeight_root hN d t x ht hx
  have hY : HasDerivAt (levelHeight d t) γ x := hasDerivAt_levelHeight hN d t x ht hx
  have hterm (j : Fin N) : HasDerivAt
      (fun a => Real.log ((a-d j)^2+(levelHeight d t a)^2))
      ((2*(x-d j)+2*y*γ)/((x-d j)^2+y^2)) x := by
    simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,id_eq,y,Pi.add_apply,Pi.pow_apply] using
      ((((hasDerivAt_id x).sub_const (d j)).pow 2).add (hY.pow 2)).log
        (ne_of_gt (level_denominator_pos _ _ hr.1))
  have hmain := ((((hasDerivAt_id x).sub_const E).pow 2).sub (hY.pow 2)).div_const (2*t)
  have hs := ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j)).const_mul
    (N : ℝ)⁻¹).div_const 2
  have h := hmain.add hs
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,id_eq] at h
  apply h.congr_deriv
  have he : realMean (fun j => (2*(x-d j)+2*y*γ)/((x-d j)^2+y^2)) =
      2*realMean (fun j => (x-d j)/((x-d j)^2+y^2))+2*y*γ*verticalLevel d x y := by
    have htermEq (j : Fin N) :
        (2*(x-d j)+2*y*γ)/((x-d j)^2+y^2) =
          2*((x-d j)/((x-d j)^2+y^2))+2*y*γ*((x-d j)^2+y^2)⁻¹ := by
      simp only [div_eq_mul_inv]
      ring
    calc
      _ = realMean (fun j =>
          2*((x-d j)/((x-d j)^2+y^2))+2*y*γ*((x-d j)^2+y^2)⁻¹) := by
        congr 1
        funext j
        exact htermEq j
      _ = _ := by
        unfold realMean verticalLevel realMean
        simp only [Finset.sum_add_distrib,← Finset.mul_sum]
        ring
  change (2*(x-E)-2*y*γ)/(2*t)+
    realMean (fun j => (2*(x-d j)+2*y*γ)/((x-d j)^2+y^2))/2 = _
  rw [he,hr.2]
  change (2*(x-E)-2*y*γ)/(2*t)+
    (2*realMean (fun j => (x-d j)/((x-d j)^2+y^2))+2*y*γ*(1/t))/2 =
    (x+t*realMean (fun j => (x-d j)/((x-d j)^2+y^2))-E)/t
  field_simp [ne_of_gt ht]
  ring

/-- The graph stays on or below the vertical level `1/t`. -/
theorem levelGraph_level_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) : verticalLevel d x (levelHeight d t x) ≤ 1/t := by
  by_cases hx : LevelActive d t x
  · exact le_of_eq (levelHeight_root hN d t x ht hx).2
  · rw [levelHeight_eq_zero hN d t x ht hx]
    exact le_of_not_gt (fun h => hx (Or.inr h))

/-- The imaginary defect vanishes on the graph: `y(x) (1 - t · level) = 0`. -/
theorem levelGraph_height_mul_defect {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) :
    levelHeight d t x*(1-t*verticalLevel d x (levelHeight d t x)) = 0 := by
  by_cases hx : LevelActive d t x
  · rw [(levelHeight_root hN d t x ht hx).2]
    field_simp [ne_of_gt ht]
    ring
  · rw [levelHeight_eq_zero hN d t x ht hx]
    ring

private theorem realMean_add {N : ℕ} (f g : Fin N → ℝ) :
    realMean (fun j => f j+g j) = realMean f+realMean g := by
  simp only [realMean,Finset.sum_add_distrib,mul_add]
private theorem realMean_sub {N : ℕ} (f g : Fin N → ℝ) :
    realMean (fun j => f j-g j) = realMean f-realMean g := by
  simp only [realMean,Finset.sum_sub_distrib,mul_sub]
private theorem realMean_mul {N : ℕ} (c : ℝ) (f : Fin N → ℝ) :
    realMean (fun j => c*f j) = c*realMean f := by
  simp only [realMean,← Finset.mul_sum]
  ring
private theorem realMean_pos {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ)
    (hf : ∀ j, 0 < f j) : 0 < realMean f := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs : 0 < ∑ j, f j := Finset.sum_pos (fun j _ => hf j)
    ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  exact mul_pos (inv_pos.mpr hn) hs

/-- The two-point cross term of the inverse squared distances along the graph. -/
def levelGraphCross {N : ℕ} (d : Fin N → ℝ) (t x₁ x₂ : ℝ) : ℝ :=
  realMean (fun j => ((x₁-d j)*(x₂-d j)-levelHeight d t x₁*levelHeight d t x₂)/
    (((x₁-d j)^2+(levelHeight d t x₁)^2)*
      ((x₂-d j)^2+(levelHeight d t x₂)^2)))

/-- For distinct graph abscissas, the two-point cross term is strictly less than `1/t`. -/
theorem levelGraphCross_lt {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x₁ x₂ : ℝ) (ht : 0 < t) (hx : x₁ ≠ x₂) :
    levelGraphCross d t x₁ x₂ < 1/t := by
  let y₁ := levelHeight d t x₁
  let y₂ := levelHeight d t x₂
  let Q := realMean (fun j =>
    (((x₁-d j)^2+y₁^2)*((x₂-d j)^2+y₂^2))⁻¹)
  have hQ : 0 < Q := realMean_pos hN _ (fun j => inv_pos.mpr
    (mul_pos (levelGraph_denominator_pos hN d t x₁ ht j)
      (levelGraph_denominator_pos hN d t x₂ ht j)))
  have he : 2*levelGraphCross d t x₁ x₂ =
      verticalLevel d x₁ y₁+verticalLevel d x₂ y₂-
        ((x₂-x₁)^2+(y₁+y₂)^2)*Q := by
    have heterm (j : Fin N) :
        2*(((x₁-d j)*(x₂-d j)-y₁*y₂)/
          (((x₁-d j)^2+y₁^2)*((x₂-d j)^2+y₂^2))) =
        ((x₁-d j)^2+y₁^2)⁻¹+((x₂-d j)^2+y₂^2)⁻¹-
          ((x₂-x₁)^2+(y₁+y₂)^2)*
            (((x₁-d j)^2+y₁^2)*((x₂-d j)^2+y₂^2))⁻¹ := by
      have hD₁ : (x₁-d j)^2+y₁^2 ≠ 0 :=
        ne_of_gt (levelGraph_denominator_pos hN d t x₁ ht j)
      have hD₂ : (x₂-d j)^2+y₂^2 ≠ 0 :=
        ne_of_gt (levelGraph_denominator_pos hN d t x₂ ht j)
      field_simp [hD₁,hD₂,mul_ne_zero hD₁ hD₂]
      ring
    change 2*realMean _ = _
    rw [← realMean_mul]
    conv_lhs => arg 1; ext j; rw [heterm]
    rw [realMean_sub,realMean_add,realMean_mul]
    rfl
  have h₁ := levelGraph_level_le hN d t x₁ ht
  have h₂ := levelGraph_level_le hN d t x₂ ht
  have hs : 0 < (x₂-x₁)^2+(y₁+y₂)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hx)))
      (sq_nonneg _)
  have hp := mul_pos hs hQ
  nlinarith [he]

/-- A two-point identity for the horizontal coordinate `ψ` along the graph. -/
theorem levelPsi_two_point_identity {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x₁ x₂ : ℝ) (ht : 0 < t) :
    (x₂-x₁)*(levelPsi d t x₂-levelPsi d t x₁) =
      ((x₂-x₁)^2+(levelHeight d t x₂-levelHeight d t x₁)^2)*
        (1-t*levelGraphCross d t x₁ x₂) := by
  let y₁ := levelHeight d t x₁
  let y₂ := levelHeight d t x₂
  let δ := x₂-x₁
  let ε := y₂-y₁
  have heterm (j : Fin N) :
      δ*((x₂-d j)/((x₂-d j)^2+y₂^2)-(x₁-d j)/((x₁-d j)^2+y₁^2))+
        ε*(-y₂*((x₂-d j)^2+y₂^2)⁻¹+y₁*((x₁-d j)^2+y₁^2)⁻¹) =
      -(δ^2+ε^2)*(((x₁-d j)*(x₂-d j)-y₁*y₂)/
        (((x₁-d j)^2+y₁^2)*((x₂-d j)^2+y₂^2))) := by
    dsimp only [δ,ε]
    have hD₁ : (x₁-d j)^2+y₁^2 ≠ 0 :=
      ne_of_gt (levelGraph_denominator_pos hN d t x₁ ht j)
    have hD₂ : (x₂-d j)^2+y₂^2 ≠ 0 :=
      ne_of_gt (levelGraph_denominator_pos hN d t x₂ ht j)
    field_simp [hD₁,hD₂,mul_ne_zero hD₁ hD₂]
    ring
  have he := congrArg (fun f : Fin N → ℝ => realMean f) (funext heterm)
  simp only [realMean_add,realMean_sub,realMean_mul] at he
  have h₁ := levelGraph_height_mul_defect hN d t x₁ ht
  have h₂ := levelGraph_height_mul_defect hN d t x₂ ht
  change y₁*(1-t*verticalLevel d x₁ y₁)=0 at h₁
  change y₂*(1-t*verticalLevel d x₂ y₂)=0 at h₂
  change δ*(realMean (fun j => (x₂-d j)/((x₂-d j)^2+y₂^2))-
      realMean (fun j => (x₁-d j)/((x₁-d j)^2+y₁^2)))+
      ε*(-y₂*verticalLevel d x₂ y₂+y₁*verticalLevel d x₁ y₁) =
    -(δ^2+ε^2)*levelGraphCross d t x₁ x₂ at he
  change δ*((x₂+t*realMean (fun j => (x₂-d j)/((x₂-d j)^2+y₂^2)))-
    (x₁+t*realMean (fun j => (x₁-d j)/((x₁-d j)^2+y₁^2)))) =
    (δ^2+ε^2)*(1-t*levelGraphCross d t x₁ x₂)
  have hε : ε=t*(y₂*verticalLevel d x₂ y₂-y₁*verticalLevel d x₁ y₁) := by
    dsimp only [ε]
    nlinarith [h₁,h₂]
  have hδ : δ*(x₂-x₁)=δ^2 := by dsimp only [δ]; ring
  have htHe := congrArg (fun a : ℝ => t*a) he
  have hεHe := congrArg (fun a : ℝ => ε*a) hε
  nlinarith [htHe,hεHe,hδ]

/-- The horizontal coordinate `ψ` is strictly increasing on `ℝ`, for every `N > 0`, `t > 0`. -/
theorem levelPsi_strictMono {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t : ℝ) (ht : 0 < t) : StrictMono (levelPsi d t) := by
  intro x₁ x₂ hx
  have hd : 0 < x₂-x₁ := sub_pos.mpr hx
  have hcross := levelGraphCross_lt hN d t x₁ x₂ ht (ne_of_lt hx)
  have hc : 0 < 1-t*levelGraphCross d t x₁ x₂ := by
    have hh := (mul_lt_mul_of_pos_left hcross ht)
    have he : t*(1/t)=1 := by field_simp [ne_of_gt ht]
    rw [he] at hh
    linarith
  have hn : 0 < (x₂-x₁)^2+(levelHeight d t x₂-levelHeight d t x₁)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hd) (sq_nonneg _)
  have hp := mul_pos hn hc
  rw [← levelPsi_two_point_identity hN d t x₁ x₂ ht] at hp
  have hdiff : 0 < levelPsi d t x₂-levelPsi d t x₁ :=
    (mul_pos_iff_of_pos_left hd).mp hp
  exact sub_pos.mp hdiff

private theorem realMean_le {N : ℕ} (f g : Fin N → ℝ)
    (hf : ∀ j, f j ≤ g j) : realMean f ≤ realMean g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hf j))
    (inv_nonneg.mpr (Nat.cast_nonneg N))

/-- The horizontal coordinate differs from the identity by at most `√t`: `(ψ(x) - x)² ≤ t`. -/
theorem levelPsi_sub_sq_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) : (levelPsi d t x-x)^2 ≤ t := by
  let y := levelHeight d t x
  let f : Fin N → ℝ := fun j => (x-d j)/((x-d j)^2+y^2)
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have hCS : (realMean f)^2 ≤ realMean (fun j => (f j)^2) := by
    simpa only [realMean,Fintype.card_fin,div_eq_mul_inv,mul_comm] using
      square_mean_le_mean_square f
  have hterm (j : Fin N) : (f j)^2 ≤ ((x-d j)^2+y^2)⁻¹ := by
    have hp : 0 < (x-d j)^2+y^2 := levelGraph_denominator_pos hN d t x ht j
    have hden : (x-d j)^2+y^2 ≠ 0 := ne_of_gt hp
    dsimp only [f]
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    have he : ((x-d j)^2+y^2)⁻¹*((x-d j)^2+y^2)^2 = (x-d j)^2+y^2 := by
      field_simp [hden]
    rw [he]
    exact le_add_of_nonneg_right (sq_nonneg y)
  have hm : (realMean f)^2 ≤ 1/t :=
    le_trans (le_trans hCS (realMean_le _ _ hterm)) (levelGraph_level_le hN d t x ht)
  have hs := mul_le_mul_of_nonneg_left hm (sq_nonneg t)
  have he : t^2*(1/t)=t := by field_simp [ne_of_gt ht]
  rw [he] at hs
  have hx : levelPsi d t x-x=t*realMean f := by unfold levelPsi; dsimp only [f,y]; ring
  rw [hx,mul_pow]
  exact hs

/-- The bound `|ψ(x) - x| ≤ √t`. -/
theorem levelPsi_sub_abs_le_sqrt {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) : |levelPsi d t x-x| ≤ Real.sqrt t := by
  apply abs_le_of_sq_le_sq _ (Real.sqrt_nonneg t)
  rw [Real.sq_sqrt (le_of_lt ht)]
  exact levelPsi_sub_sq_le hN d t x ht

/-- The real part of the finite Stieltjes transform. -/
theorem finiteStieltjes_re {N : ℕ} (d : Fin N → ℝ) (z : ℂ) :
    (finiteStieltjes d z).re =
      -realMean (fun j => (z.re-d j)/((z.re-d j)^2+z.im^2)) := by
  unfold finiteStieltjes complexMean realMean
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [show (∑ j, ((d j : ℂ)-z)⁻¹).re = ∑ j, (((d j : ℂ)-z)⁻¹).re from
    map_sum Complex.reAddGroupHom _ _]
  simp only [Complex.inv_re,normSq_real_sub,Complex.sub_re,Complex.ofReal_re]
  have he (j : Fin N) : (d j-z.re)/((d j-z.re)^2+z.im^2) =
      -((z.re-d j)/((z.re-d j)^2+z.im^2)) := by
    rw [show (d j-z.re)^2=(z.re-d j)^2 by ring]
    ring
  simp_rw [he]
  rw [Finset.sum_neg_distrib]
  ring

/-- At a solution `m` of the finite MDE with `Im m > 0`, `ψ = E` at the real part of the saddle
point. -/
theorem levelPsi_at_saddle {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t : ℝ) (m : ℂ) (ht : 0 < t) (hm : 0 < m.im)
    (hMDE : FiniteMDE d E t m) : levelPsi d t (saddlePoint E t m).re = E := by
  have he := congrArg Complex.re hMDE
  rw [finiteStieltjes_re] at he
  have hx : (saddlePoint E t m).re=E+t*m.re := by simp [saddlePoint,Complex.mul_re]
  unfold levelPsi
  rw [levelHeight_at_saddle hN d E t m ht hm hMDE]
  nlinarith [congrArg (fun a : ℝ => t*a) he,hx]

/-- At a solution of the finite MDE, `ψ(x) = E` holds exactly at the real part of the saddle
point. -/
theorem levelPsi_eq_energy_iff_saddle {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t : ℝ) (m : ℂ) (ht : 0 < t) (hm : 0 < m.im)
    (hMDE : FiniteMDE d E t m) (x : ℝ) :
    levelPsi d t x=E ↔ x=(saddlePoint E t m).re := by
  have he := levelPsi_at_saddle hN d E t m ht hm hMDE
  constructor
  · intro hx
    exact (levelPsi_strictMono hN d t ht).injective (hx.trans he.symm)
  · intro hx
    rw [hx]
    exact he

/-- The real part of the principal logarithm of `x + iy - d` is `log((x - d)² + y²)/2`. -/
theorem log_graph_real_part (x y d : ℝ) :
    (Complex.log ((x : ℂ)+(y : ℂ)*Complex.I-(d : ℂ))).re =
      Real.log ((x-d)^2+y^2)/2 := by
  let z : ℂ := (x : ℂ)+(y : ℂ)*Complex.I-(d : ℂ)
  have hn : Complex.normSq z=(x-d)^2+y^2 := by
    simp only [z,Complex.normSq_apply,Complex.add_re,Complex.sub_re,Complex.ofReal_re,
      Complex.mul_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,mul_zero,
      sub_zero,add_zero,Complex.add_im,Complex.sub_im,Complex.mul_im,mul_one,zero_add]
    ring
  rw [Complex.log_re]
  change Real.log ‖z‖=Real.log ((x-d)^2+y^2)/2
  rw [← hn,Complex.normSq_eq_norm_sq,Real.log_pow]
  norm_num

/-- The level action is the real part of the Johansson saddle phase on the graph. -/
theorem levelAction_eq_saddlePhase_re {N : ℕ} (d : Fin N → ℝ)
    (E t x : ℝ) :
    levelAction d E t x =
      (saddlePhase d E t ((x : ℂ)+(levelHeight d t x : ℂ)*Complex.I)).re := by
  let y := levelHeight d t x
  have hquad :
      (((((x : ℂ)+(y : ℂ)*Complex.I)-(E : ℂ))^2)/(2*(t : ℂ))).re =
        ((x-E)^2-y^2)/(2*t) := by
    rw [show 2*(t : ℂ)=((2*t : ℝ):ℂ) by norm_cast,Complex.div_ofReal_re]
    simp only [pow_two,Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.ofReal_re,
      Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,sub_zero,add_zero,
      Complex.add_im,Complex.sub_im,Complex.mul_im,mul_one,zero_add]
  have hmean : (complexMean (fun j => Complex.log
      ((x : ℂ)+(y : ℂ)*Complex.I-(d j : ℂ)))).re =
        realMean (fun j => Real.log ((x-d j)^2+y^2))/2 := by
    unfold complexMean realMean
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [show (∑ j,Complex.log ((x : ℂ)+(y : ℂ)*Complex.I-(d j : ℂ))).re =
      ∑ j,(Complex.log ((x : ℂ)+(y : ℂ)*Complex.I-(d j : ℂ))).re from
      map_sum Complex.reAddGroupHom _ _]
    simp_rw [log_graph_real_part]
    simp only [div_eq_mul_inv,← Finset.sum_mul]
    ring
  unfold saddlePhase levelAction
  rw [Complex.add_re]
  change _= _
  rw [hquad,hmean]

end
end BlockBand.GaussianBulk
