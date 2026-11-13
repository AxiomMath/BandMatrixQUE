module

public import Mathlib
public import BlockBand.GaussianBulk.SaddleIdentities

/-!
# The level graph of the external-source saddle

For a finite real source `d` and `t > 0`, `levelHeight d t x` is the unique positive root `y` of
`N⁻¹ Σ_j ((x - d_j)² + y²)⁻¹ = 1/t` when one exists, and `0` otherwise. The root exists exactly
on an open active set containing every pole; the graph lies in the strip `0 ≤ y ≤ √t`, is
continuous on `ℝ`, and passes through the saddle point of the finite MDE.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.GaussianBulk

open scoped BigOperators

/-- The normalized inverse-square level `N⁻¹ Σ_j ((x - d_j)² + y²)⁻¹`. -/
def verticalLevel {N : ℕ} (d : Fin N → ℝ) (x y : ℝ) : ℝ :=
  realMean (fun j => ((x-d j)^2+y^2)⁻¹)

/-- The active domain: `x` is a pole, or the level at height `0` exceeds `1/t` (at a pole the
boundary level is infinite, although Lean's real inverse at zero is zero). -/
def LevelActive {N : ℕ} (d : Fin N → ℝ) (t x : ℝ) : Prop :=
  (∃ j, x = d j) ∨ 1/t < verticalLevel d x 0

/-- `y` is a positive root of the level equation. -/
def PositiveLevelRoot {N : ℕ} (d : Fin N → ℝ) (t x y : ℝ) : Prop :=
  0 < y ∧ verticalLevel d x y = 1/t

/-- The level height: a positive root of the level equation if one exists, `0` otherwise. -/
def levelHeight {N : ℕ} (d : Fin N → ℝ) (t x : ℝ) : ℝ := by
  classical
  exact if h : ∃ y, PositiveLevelRoot d t x y then Classical.choose h else 0

/-- The level in real coordinates equals `levelAverage`. -/
theorem verticalLevel_eq_levelAverage {N : ℕ} (d : Fin N → ℝ) (x y : ℝ) :
    verticalLevel d x y = levelAverage d ⟨x,y⟩ := by
  unfold verticalLevel levelAverage
  simp only [normSq_real_sub]
  congr 1
  funext j
  congr 1
  ring

/-- Each denominator is strictly positive at positive height. -/
theorem level_denominator_pos (a y : ℝ) (hy : 0 < y) : 0 < a^2+y^2 := by
  positivity

/-- The level is strictly decreasing between nonnegative heights whenever the denominators at
the lower height are nonzero. -/
theorem verticalLevel_lt_of_lt {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (x a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hden : ∀ j, 0 < (x-d j)^2+a^2) :
    verticalLevel d x b < verticalLevel d x a := by
  have hNp : 0 < (N : ℝ)⁻¹ := by exact inv_pos.mpr (by exact_mod_cast hN)
  have hsum : (∑ j, ((x-d j)^2+b^2)⁻¹) <
      ∑ j, ((x-d j)^2+a^2)⁻¹ := by
    apply Finset.sum_lt_sum_of_nonempty
      (show (Finset.univ : Finset (Fin N)).Nonempty from ⟨⟨0,hN⟩,Finset.mem_univ _⟩)
    intro j _
    apply inv_strictAnti₀ (hden j)
    nlinarith
  exact mul_lt_mul_of_pos_left hsum hNp

/-- The level is strictly decreasing on positive heights. -/
theorem verticalLevel_strictAntiOn {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (x : ℝ) : StrictAntiOn (verticalLevel d x) (Set.Ioi 0) := by
  intro a ha b _ hab
  exact verticalLevel_lt_of_lt hN d x a b (le_of_lt ha) hab
    (fun j => level_denominator_pos (x-d j) a ha)

/-- The level is continuous on any set of heights avoiding all zero denominators. -/
theorem verticalLevel_continuousOn {N : ℕ} (d : Fin N → ℝ) (x : ℝ)
    (s : Set ℝ) (hs : ∀ y ∈ s, ∀ j, (x-d j)^2+y^2 ≠ 0) :
    ContinuousOn (verticalLevel d x) s := by
  unfold verticalLevel realMean
  apply continuousOn_const.mul
  apply continuousOn_finsetSum
  intro j _
  exact (continuousOn_const.add (continuousOn_id.pow 2)).inv₀
    (fun y hy => hs y hy j)

/-- The dimension-free bound `level ≤ y⁻²`. -/
theorem verticalLevel_le_inv_sq {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (x y : ℝ) (hy : 0 < y) : verticalLevel d x y ≤ (y^2)⁻¹ := by
  have hsum : (∑ j, ((x-d j)^2+y^2)⁻¹) ≤ ∑ _j : Fin N, (y^2)⁻¹ := by
    apply Finset.sum_le_sum
    intro j _
    exact inv_anti₀ (by positivity : 0 < y^2)
      (by nlinarith [sq_nonneg (x-d j)])
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have h := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (N : ℝ)⁻¹ by positivity)
  simpa [verticalLevel, realMean, hn] using h

/-- At height `√t` the level is at most `1/t`. -/
theorem verticalLevel_sqrt_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) : verticalLevel d x (Real.sqrt t) ≤ 1/t := by
  simpa [Real.sq_sqrt (le_of_lt ht), one_div] using
    verticalLevel_le_inv_sq hN d x (Real.sqrt t) (Real.sqrt_pos.mpr ht)

/-- Every positive root has height at most `√t`. -/
theorem positiveLevelRoot_le_sqrt {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x y : ℝ) (ht : 0 < t) (hy : PositiveLevelRoot d t x y) :
    y ≤ Real.sqrt t := by
  have h := verticalLevel_le_inv_sq hN d x y hy.1
  rw [hy.2, ← one_div] at h
  have hs : y^2 ≤ t := (one_div_le_one_div ht (sq_pos_of_pos hy.1)).mp h
  nlinarith [Real.sq_sqrt (le_of_lt ht), Real.sqrt_nonneg t]

/-- A positive height `a ≤ √t` with level at least `1/t` gives a positive root, by the
intermediate value theorem. -/
theorem positiveLevelRoot_of_bracket {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x a : ℝ) (ht : 0 < t) (ha : 0 < a) (hab : a ≤ Real.sqrt t)
    (hlevel : 1/t ≤ verticalLevel d x a) : ∃ y, PositiveLevelRoot d t x y := by
  have hc : ContinuousOn (verticalLevel d x) (Set.Icc a (Real.sqrt t)) :=
    verticalLevel_continuousOn d x _ (fun y hy j =>
      ne_of_gt (level_denominator_pos (x-d j) y (lt_of_lt_of_le ha hy.1)))
  obtain ⟨y, hy, heq⟩ := intermediate_value_Icc' hab hc
    ⟨verticalLevel_sqrt_le hN d t x ht, hlevel⟩
  exact ⟨y,lt_of_lt_of_le ha hy.1,heq⟩

/-- At a pole, the height `√(t/(2N))` has level at least `2/t`. -/
theorem verticalLevel_at_pole_lower {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t : ℝ) (ht : 0 < t) (j : Fin N) :
    2/t ≤ verticalLevel d (d j) (Real.sqrt (t/(2*(N : ℝ)))) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hy : 0 < t/(2*(N : ℝ)) := by positivity
  have hsum : ((d j-d j)^2+(Real.sqrt (t/(2*(N : ℝ))))^2)⁻¹ ≤
      ∑ k, ((d j-d k)^2+(Real.sqrt (t/(2*(N : ℝ))))^2)⁻¹ := by
    exact Finset.single_le_sum
      (f := fun k => ((d j-d k)^2+(Real.sqrt (t/(2*(N : ℝ))))^2)⁻¹)
      (fun k _ => by positivity) (Finset.mem_univ j)
  have h := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (N : ℝ)⁻¹ by positivity)
  have heq : (N : ℝ)⁻¹ *
      ((d j-d j)^2+(Real.sqrt (t/(2*(N : ℝ))))^2)⁻¹ = 2/t := by
    rw [Real.sq_sqrt (le_of_lt hy)]
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_add]
    field_simp
  rw [heq] at h
  exact h

/-- Every pole has a positive root, including repeated poles. -/
theorem positiveLevelRoot_exists_at_pole {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t : ℝ) (ht : 0 < t) (j : Fin N) :
    ∃ y, PositiveLevelRoot d t (d j) y := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ha : 0 < Real.sqrt (t/(2*(N : ℝ))) := Real.sqrt_pos.mpr (by positivity)
  have hab : Real.sqrt (t/(2*(N : ℝ))) ≤ Real.sqrt t := by
    apply Real.sqrt_le_sqrt
    apply (div_le_iff₀ (by positivity : 0 < 2*(N : ℝ))).mpr
    nlinarith
  apply positiveLevelRoot_of_bracket hN d t (d j) _ ht ha hab
  exact le_trans
    (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt ht))
    (verticalLevel_at_pole_lower hN d t ht j)

/-- Away from poles, a level at height `0` above `1/t` gives a positive root. -/
theorem positiveLevelRoot_exists_off_poles {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t x : ℝ) (ht : 0 < t) (hp : ∀ j, x ≠ d j)
    (hlevel : 1/t < verticalLevel d x 0) : ∃ y, PositiveLevelRoot d t x y := by
  have hc : ContinuousOn (verticalLevel d x) (Set.Icc 0 (Real.sqrt t)) :=
    verticalLevel_continuousOn d x _ (fun y _ j => by
      have hs : 0 < (x-d j)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (hp j))
      nlinarith [sq_nonneg y])
  obtain ⟨y, hy, heq⟩ := intermediate_value_Icc' (Real.sqrt_nonneg t) hc
    ⟨verticalLevel_sqrt_le hN d t x ht, le_of_lt hlevel⟩
  have hne : y ≠ 0 := by
    intro h
    rw [h] at heq
    linarith
  exact ⟨y,lt_of_le_of_ne hy.1 (Ne.symm hne),heq⟩

/-- A positive root exists exactly on the active domain. -/
theorem positiveLevelRoot_exists_iff {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) :
    (∃ y, PositiveLevelRoot d t x y) ↔ LevelActive d t x := by
  constructor
  · rintro ⟨y,hy⟩
    by_cases hp : ∃ j, x = d j
    · exact Or.inl hp
    · right
      have hden (j : Fin N) : 0 < (x-d j)^2+(0 : ℝ)^2 := by
        have hne : x ≠ d j := fun h => hp ⟨j,h⟩
        simpa using sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
      have h := verticalLevel_lt_of_lt hN d x 0 y le_rfl hy.1 hden
      rwa [hy.2] at h
  · intro ha
    rcases ha with ⟨j,hj⟩ | hlevel
    · rw [hj]
      exact positiveLevelRoot_exists_at_pole hN d t ht j
    · by_cases hp : ∃ j, x = d j
      · obtain ⟨j,hj⟩ := hp
        rw [hj]
        exact positiveLevelRoot_exists_at_pole hN d t ht j
      · exact positiveLevelRoot_exists_off_poles hN d t x ht
          (fun j h => hp ⟨j,h⟩) hlevel

/-- Positive roots are unique. -/
theorem positiveLevelRoot_unique {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x a b : ℝ) (ha : PositiveLevelRoot d t x a)
    (hb : PositiveLevelRoot d t x b) : a = b := by
  apply (verticalLevel_strictAntiOn hN d x).injOn ha.1 hb.1
  exact ha.2.trans hb.2.symm

/-- At every active point the level height is the positive root. -/
theorem levelHeight_root {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) (ha : LevelActive d t x) :
    PositiveLevelRoot d t x (levelHeight d t x) := by
  have he := (positiveLevelRoot_exists_iff hN d t x ht).mpr ha
  unfold levelHeight
  rw [dite_eq_left he]
  exact Classical.choose_spec he

/-- Off the active domain the level height is zero. -/
theorem levelHeight_eq_zero {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) (ha : ¬LevelActive d t x) : levelHeight d t x = 0 := by
  have he : ¬∃ y, PositiveLevelRoot d t x y :=
    fun h => ha ((positiveLevelRoot_exists_iff hN d t x ht).mp h)
  unfold levelHeight
  rw [dite_eq_right he]

/-- The level height lies in `[0, √t]`. -/
theorem levelHeight_bounds {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) :
    0 ≤ levelHeight d t x ∧ levelHeight d t x ≤ Real.sqrt t := by
  by_cases ha : LevelActive d t x
  · have hr := levelHeight_root hN d t x ht ha
    exact ⟨le_of_lt hr.1,positiveLevelRoot_le_sqrt hN d t x _ ht hr⟩
  · rw [levelHeight_eq_zero hN d t x ht ha]
    exact ⟨le_rfl,Real.sqrt_nonneg t⟩

/-- The level height is positive at every pole. -/
theorem levelHeight_at_pole_pos {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t : ℝ) (ht : 0 < t) (j : Fin N) : 0 < levelHeight d t (d j) :=
  (levelHeight_root hN d t (d j) ht (Or.inl ⟨j,rfl⟩)).1

/-- Every positive root lies horizontally within `√t` of some pole. -/
theorem positiveLevelRoot_near_pole {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x y : ℝ) (ht : 0 < t) (hy : PositiveLevelRoot d t x y) :
    ∃ j, |x-d j| < Real.sqrt t := by
  by_contra hp
  have hd (j : Fin N) : t < (x-d j)^2+y^2 := by
    have ha : Real.sqrt t ≤ |x-d j| := le_of_not_gt (fun h => hp ⟨j,h⟩)
    have hs := mul_self_le_mul_self (Real.sqrt_nonneg t) ha
    rw [← pow_two, ← pow_two, sq_abs, Real.sq_sqrt (le_of_lt ht)] at hs
    nlinarith [sq_pos_of_pos hy.1]
  have hsum : (∑ j, ((x-d j)^2+y^2)⁻¹) < ∑ _j : Fin N, 1/t := by
    apply Finset.sum_lt_sum_of_nonempty
      (show (Finset.univ : Finset (Fin N)).Nonempty from ⟨⟨0,hN⟩,Finset.mem_univ _⟩)
    intro j _
    simpa [one_div] using inv_strictAnti₀ ht (hd j)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have h := mul_lt_mul_of_pos_left hsum
    (show 0 < (N : ℝ)⁻¹ from inv_pos.mpr (by exact_mod_cast hN))
  have h' : verticalLevel d x y < 1/t := by
    simpa [verticalLevel,realMean,hn] using h
  rw [hy.2] at h'
  exact lt_irrefl _ h'

/-- The level height is positive exactly on the active domain. -/
theorem levelHeight_pos_iff {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) : 0 < levelHeight d t x ↔ LevelActive d t x := by
  constructor
  · intro hp
    by_contra ha
    rw [levelHeight_eq_zero hN d t x ht ha] at hp
    exact lt_irrefl _ hp
  · intro ha
    exact (levelHeight_root hN d t x ht ha).1

/-- A positive root is the level height. -/
theorem levelHeight_eq_of_root {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x y : ℝ) (ht : 0 < t) (hy : PositiveLevelRoot d t x y) :
    levelHeight d t x = y := by
  have ha := (positiveLevelRoot_exists_iff hN d t x ht).mp ⟨y,hy⟩
  exact positiveLevelRoot_unique hN d t x _ y (levelHeight_root hN d t x ht ha) hy

/-- The saddle point of a solution of the finite MDE lies on the level graph (the Ward identity
gives the root, and uniqueness identifies it). -/
theorem levelHeight_at_saddle {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t : ℝ) (m : ℂ) (ht : 0 < t) (hm : 0 < m.im)
    (hMDE : FiniteMDE d E t m) :
    levelHeight d t (saddlePoint E t m).re = (saddlePoint E t m).im := by
  apply levelHeight_eq_of_root hN d t _ _ ht
  constructor
  · rw [saddlePoint_im]
    exact mul_pos ht hm
  · rw [verticalLevel_eq_levelAverage]
    exact levelAverage_saddle_eq d E t m ht hm hMDE

/-- If all poles lie in `[lo, hi]`, the graph has positive height only on
`(lo - √t, hi + √t)`. -/
theorem levelHeight_support_interval {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x lo hi : ℝ) (ht : 0 < t) (hd : ∀ j, lo ≤ d j ∧ d j ≤ hi)
    (hx : 0 < levelHeight d t x) :
    lo-Real.sqrt t < x ∧ x < hi+Real.sqrt t := by
  have hr := levelHeight_root hN d t x ht ((levelHeight_pos_iff hN d t x ht).mp hx)
  obtain ⟨j,hj⟩ := positiveLevelRoot_near_pole hN d t x _ ht hr
  have ha := abs_lt.mp hj
  constructor <;> linarith [(hd j).1,(hd j).2]

/-- At fixed positive height the level is continuous in `x`, also across the poles. -/
theorem verticalLevel_continuous_x {N : ℕ} (d : Fin N → ℝ)
    (y : ℝ) (hy : 0 < y) : Continuous (fun x => verticalLevel d x y) := by
  unfold verticalLevel realMean
  apply continuous_const.mul
  apply continuous_finsetSum
  intro j _
  exact (((continuous_id.sub continuous_const).pow 2).add continuous_const).inv₀
    (fun x => ne_of_gt (level_denominator_pos (x-d j) y hy))

/-- `x` is active iff some positive height has level strictly above `1/t`. -/
theorem levelActive_iff_positive_witness {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t x : ℝ) (ht : 0 < t) :
    LevelActive d t x ↔ ∃ y, 0 < y ∧ 1/t < verticalLevel d x y := by
  constructor
  · intro ha
    have hr := levelHeight_root hN d t x ht ha
    refine ⟨levelHeight d t x/2,by linarith [hr.1],?_⟩
    have h := verticalLevel_lt_of_lt hN d x (levelHeight d t x/2)
      (levelHeight d t x) (by linarith [hr.1]) (by linarith [hr.1])
      (fun j => level_denominator_pos (x-d j) _ (by linarith [hr.1]))
    rwa [hr.2] at h
  · rintro ⟨y,hy,hlevel⟩
    by_cases hp : ∃ j, x = d j
    · exact Or.inl hp
    · right
      have hden (j : Fin N) : 0 < (x-d j)^2+(0 : ℝ)^2 := by
        simpa using sq_pos_of_ne_zero (sub_ne_zero.mpr (fun h => hp ⟨j,h⟩))
      exact lt_trans hlevel (verticalLevel_lt_of_lt hN d x 0 y le_rfl hy hden)

/-- The active domain is open. -/
theorem isOpen_levelActive {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t : ℝ) (ht : 0 < t) : IsOpen {x | LevelActive d t x} := by
  have hset : {x | LevelActive d t x} =
      ⋃ y : {y : ℝ // 0 < y}, {x | 1/t < verticalLevel d x y.val} := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,hlevel⟩ := (levelActive_iff_positive_witness hN d t x ht).mp hx
      exact Set.mem_iUnion.mpr ⟨⟨y,hy⟩,hlevel⟩
    · intro hx
      obtain ⟨y,hy⟩ := Set.mem_iUnion.mp hx
      exact (levelActive_iff_positive_witness hN d t x ht).mpr ⟨y.val,y.property,hy⟩
  rw [hset]
  exact isOpen_iUnion (fun y => isOpen_lt continuous_const
    (verticalLevel_continuous_x d y.val y.property))

/-- `a < y(x)` iff the level at height `a > 0` exceeds `1/t`. -/
theorem levelHeight_gt_iff {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x a : ℝ) (ht : 0 < t) (ha : 0 < a) :
    a < levelHeight d t x ↔ 1/t < verticalLevel d x a := by
  constructor
  · intro h
    have hr := levelHeight_root hN d t x ht
      ((levelHeight_pos_iff hN d t x ht).mp (lt_trans ha h))
    have hh := verticalLevel_lt_of_lt hN d x a _ (le_of_lt ha) h
      (fun j => level_denominator_pos (x-d j) a ha)
    rwa [hr.2] at hh
  · intro h
    have hr := levelHeight_root hN d t x ht
      ((levelActive_iff_positive_witness hN d t x ht).mpr ⟨a,ha,h⟩)
    by_contra hn
    have hh := (verticalLevel_strictAntiOn hN d x).antitoneOn
      hr.1 ha (le_of_not_gt hn)
    rw [hr.2] at hh
    exact (not_lt_of_ge hh) h

/-- `y(x) < a` iff the level at height `a > 0` is below `1/t`. -/
theorem levelHeight_lt_iff {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x a : ℝ) (ht : 0 < t) (ha : 0 < a) :
    levelHeight d t x < a ↔ verticalLevel d x a < 1/t := by
  by_cases hx : LevelActive d t x
  · have hr := levelHeight_root hN d t x ht hx
    constructor
    · intro h
      have hh := verticalLevel_lt_of_lt hN d x _ a (le_of_lt hr.1) h
        (fun j => level_denominator_pos (x-d j) _ hr.1)
      rwa [hr.2] at hh
    · intro h
      by_contra hn
      have hh := (verticalLevel_strictAntiOn hN d x).antitoneOn
        ha hr.1 (le_of_not_gt hn)
      rw [hr.2] at hh
      exact (not_lt_of_ge hh) h
  · have hz := levelHeight_eq_zero hN d t x ht hx
    rw [hz]
    have hle : verticalLevel d x a ≤ 1/t := by
      apply le_of_not_gt
      intro h
      exact hx ((levelActive_iff_positive_witness hN d t x ht).mpr ⟨a,ha,h⟩)
    have hlt : verticalLevel d x a < 1/t := by
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exact False.elim (hx ((positiveLevelRoot_exists_iff hN d t x ht).mp
          ⟨a,ha,h⟩))
    exact ⟨fun _ => hlt,fun _ => ha⟩

/-- The level height is continuous on `ℝ`, including at the gap endpoints and at repeated poles. -/
theorem levelHeight_continuous {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t : ℝ) (ht : 0 < t) : Continuous (levelHeight d t) := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  constructor
  · rcases lt_trichotomy a 0 with ha | ha | ha
    · have hs : levelHeight d t ⁻¹' Set.Ioi a = Set.univ := by
        ext x
        simp only [Set.mem_preimage,Set.mem_Ioi,Set.mem_univ,iff_true]
        exact lt_of_lt_of_le ha (levelHeight_bounds hN d t x ht).1
      rw [hs]
      exact isOpen_univ
    · subst a
      have hs : levelHeight d t ⁻¹' Set.Ioi 0 = {x | LevelActive d t x} := by
        ext x
        exact levelHeight_pos_iff hN d t x ht
      rw [hs]
      exact isOpen_levelActive hN d t ht
    · have hs : levelHeight d t ⁻¹' Set.Ioi a =
          {x | 1/t < verticalLevel d x a} := by
        ext x
        exact levelHeight_gt_iff hN d t x a ht ha
      rw [hs]
      exact isOpen_lt continuous_const (verticalLevel_continuous_x d a ha)
  · by_cases ha : 0 < a
    · have hs : levelHeight d t ⁻¹' Set.Iio a =
          {x | verticalLevel d x a < 1/t} := by
        ext x
        exact levelHeight_lt_iff hN d t x a ht ha
      rw [hs]
      exact isOpen_lt (verticalLevel_continuous_x d a ha) continuous_const
    · have hs : levelHeight d t ⁻¹' Set.Iio a = (∅ : Set ℝ) := by
        ext x
        simp only [Set.mem_preimage,Set.mem_Iio,Set.mem_empty_iff_false,iff_false]
        exact not_lt_of_ge (le_trans (le_of_not_gt ha) (levelHeight_bounds hN d t x ht).1)
      rw [hs]
      exact isOpen_empty

end BlockBand.GaussianBulk
