module

public import BlockBand.Adapters.ErdosRiabov.ShortRingLocalLawProfile
public import BlockBand.Adapters.ErdosRiabov.PolynomialControl

/-!
# Powers of the short-ring profile

Support and size bounds for the entries of the powers `S^k` of the short-ring profile.

* `shortRingProfile_pow_le`: for `0 < b < 1/2`, `m ≥ 3`, `W ≥ 1`, `k ≥ 1`:
  `0 ≤ (S^k)_{xy} ≤ 1/W` (rows of `S^{k-1}` sum to one, `S ≤ 1/W`).
* `shortRingProfile_pow_eq_zero_of_far`: `(S^k)_{xy} = 0` whenever
  `cyclicDistance (mW) x y ≥ (k+1) W`, for every `k ≥ 0`, every `b`, `m` and `W`
  (`S_{xy} ≠ 0` forces cyclic block distance `≤ 1`, and site distance `≤ (j+1)W - 1` at block
  distance `j`).
  Uses `shortRingProfile_colSum`, `shortRingProfile_symm`, `shortRingProfile_nonneg`,
  `shortRingProfile_le` and `ringSucc_mod`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Kernel

open BlockBand.External BlockBand.Internal.Contracts.Inputs BlockBand.Adapters.ErdosRiabov
open scoped BigOperators

/-!
## Cyclic block distance
-/

/-- Cyclic distance on `ℤ/m` of two representatives `a, b < m`. -/
def cycDist (m a b : ℕ) : ℕ := min (max a b - min a b) (m - (max a b - min a b))

/-- The cyclic distance of the blocks `x / W`, `y / W` of two sites. -/
def blockDistance (m W : ℕ) (x y : Fin (m * W)) : ℕ := cycDist m (x.val / W) (y.val / W)

theorem cycDist_triangle {m a b c : ℕ} (ha : a < m) (hb : b < m) (hc : c < m) :
    cycDist m a c ≤ cycDist m a b + cycDist m b c := by
  unfold cycDist
  omega

theorem cycDist_comm (m a b : ℕ) : cycDist m a b = cycDist m b a := by
  unfold cycDist
  omega

theorem width_pos {m W : ℕ} (x : Fin (m * W)) : 0 < W := by
  have h := Fin.pos x
  exact Nat.pos_of_ne_zero (by rintro rfl; simp at h)

theorem block_lt {m W : ℕ} (x : Fin (m * W)) : x.val / W < m :=
  (Nat.div_lt_iff_lt_mul (width_pos x)).mpr x.isLt

theorem blockDistance_comm (m W : ℕ) (x y : Fin (m * W)) :
    blockDistance m W x y = blockDistance m W y x :=
  cycDist_comm _ _ _

theorem blockDistance_triangle {m W : ℕ} (x y z : Fin (m * W)) :
    blockDistance m W x z ≤ blockDistance m W x y + blockDistance m W y z :=
  cycDist_triangle (block_lt x) (block_lt y) (block_lt z)

theorem blockDistance_self {m W : ℕ} (x : Fin (m * W)) : blockDistance m W x x = 0 := by
  simp [blockDistance, cycDist]

/-- Linear core of the site/block comparison. -/
theorem site_block_aux {N W P Q a a' x y : ℕ} (hx : x = P + a) (hy : y = Q + a')
    (ha : a < W) (ha' : a' < W) (hPQ : Q ≤ P) (hxN : x < N) (hyx : y ≤ x) :
    min (x - y) (N - (x - y)) + 1 ≤ (P - Q) + W ∧
      min (x - y) (N - (x - y)) + 1 ≤ (N - (P - Q)) + W := by
  omega

/-- Sites at cyclic block distance `j` have cyclic site distance at most `(j+1) W - 1`. -/
theorem cyclicDistance_add_one_le {m W : ℕ} (x y : Fin (m * W)) :
    ErdosRiabov.cyclicDistance (m * W) x y + 1 ≤ (blockDistance m W x y + 1) * W := by
  wlog hxy : y.val ≤ x.val generalizing x y
  · have := this y x (by omega)
    rwa [ErdosRiabov.cyclicDistance_comm, blockDistance_comm]
  have hW := width_pos x
  have hkl : y.val / W ≤ x.val / W := Nat.div_le_div_right hxy
  have hx := Nat.div_add_mod x.val W
  have hy := Nat.div_add_mod y.val W
  have hax := Nat.mod_lt x.val hW
  have hay := Nat.mod_lt y.val hW
  have hPQ : W * (y.val / W) ≤ W * (x.val / W) := Nat.mul_le_mul_left _ hkl
  have haux := site_block_aux (N := m * W) hx.symm hy.symm hax hay hPQ x.isLt hxy
  have e1 : (x.val / W - y.val / W + 1) * W = (W * (x.val / W) - W * (y.val / W)) + W := by
    rw [add_one_mul, mul_comm, mul_tsub]
  have e2 : (m - (x.val / W - y.val / W) + 1) * W =
      (m * W - (W * (x.val / W) - W * (y.val / W))) + W := by
    rw [add_one_mul, mul_comm, mul_tsub, mul_tsub, mul_comm W m]
  simp only [ErdosRiabov.cyclicDistance, blockDistance, cycDist, max_eq_left hkl,
    min_eq_right hkl, max_eq_left hxy, min_eq_right hxy]
  rcases min_cases (x.val / W - y.val / W) (m - (x.val / W - y.val / W)) with
    ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · rw [e1]
    exact haux.1
  · rw [e2]
    exact haux.2

/-!
## Support of `S` and of its powers
-/

/-- `S_{xy} ≠ 0` forces cyclic block distance at most one. -/
theorem shortRingProfile_support {b : ℝ} {m W : ℕ} {x y : Fin (m * W)}
    (h : shortRingProfile b m W x y ≠ 0) : blockDistance m W x y ≤ 1 := by
  have hx := block_lt x
  have hy := block_lt y
  unfold shortRingProfile at h
  unfold blockDistance cycDist
  split_ifs at h with h1 h2
  · omega
  · rw [ringSucc_mod hx, ringSucc_mod hy] at h2
    generalize x.val / W = a at *
    generalize y.val / W = c at *
    split_ifs at h2 <;> omega
  · exact absurd rfl h

/-- `(S^k)_{xy} ≠ 0` forces cyclic block distance at most `k`. -/
theorem shortRingProfile_pow_support {b : ℝ} {m W : ℕ} (k : ℕ) {x y : Fin (m * W)}
    (h : (shortRingProfile b m W ^ k) x y ≠ 0) : blockDistance m W x y ≤ k := by
  induction k generalizing y with
  | zero =>
    rw [pow_zero, Matrix.one_apply] at h
    split_ifs at h with hxy
    · subst hxy
      rw [blockDistance_self]
    · exact absurd rfl h
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨z, -, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := ih (mul_ne_zero_iff.mp hz).1
    have h2 := shortRingProfile_support (mul_ne_zero_iff.mp hz).2
    have := blockDistance_triangle x z y
    omega

/-- **Support of `S^k`**:
`(S^k)_{xy} = 0` whenever `cyclicDistance (mW) x y ≥ (k+1) W`; every `k ≥ 0`, `b`, `m`, `W`. -/
theorem shortRingProfile_pow_eq_zero_of_far (b : ℝ) {m W : ℕ} (k : ℕ) {x y : Fin (m * W)}
    (hfar : (k + 1) * W ≤ ErdosRiabov.cyclicDistance (m * W) x y) :
    (shortRingProfile b m W ^ k) x y = 0 := by
  by_contra h
  have h1 := shortRingProfile_pow_support k h
  have h2 := cyclicDistance_add_one_le x y
  have h3 : (blockDistance m W x y + 1) * W ≤ (k + 1) * W :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-!
## Size of the entries of `S^k`
-/

/-- Rows of `S` sum to one (`m ≥ 3`, `W ≥ 1`). -/
theorem shortRingProfile_rowSum (b : ℝ) {m W : ℕ} (hm : 3 ≤ m) (hW : 0 < W)
    (i : Fin (m * W)) : (∑ j, shortRingProfile b m W i j) = 1 := by
  rw [← shortRingProfile_colSum b hm hW i]
  exact Finset.sum_congr rfl fun j _ => shortRingProfile_symm b m W i j

theorem shortRingProfile_pow_nonneg {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {m W : ℕ} (k : ℕ)
    (x y : Fin (m * W)) : 0 ≤ (shortRingProfile b m W ^ k) x y := by
  induction k generalizing y with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg (ih z) (shortRingProfile_nonneg hb0 hb m W z y)

/-- Rows of `S^k` sum to one. -/
theorem shortRingProfile_pow_rowSum (b : ℝ) {m W : ℕ} (hm : 3 ≤ m) (hW : 0 < W) (k : ℕ)
    (x : Fin (m * W)) : (∑ y, (shortRingProfile b m W ^ k) x y) = 1 := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    rw [Finset.sum_ite_eq]
    simp
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, shortRingProfile_rowSum b hm hW, mul_one]
    exact ih

/-- **Size of `S^k`**: for `0 < b < 1/2`,
`m ≥ 3`, `W ≥ 1` and `k ≥ 1`, `0 ≤ (S^k)_{xy} ≤ 1/W`. -/
theorem shortRingProfile_pow_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {m W : ℕ} (hm : 3 ≤ m)
    (hW : 0 < W) {k : ℕ} (hk : 1 ≤ k) (x y : Fin (m * W)) :
    0 ≤ (shortRingProfile b m W ^ k) x y ∧
      (shortRingProfile b m W ^ k) x y ≤ 1 / (W : ℝ) := by
  refine ⟨shortRingProfile_pow_nonneg hb0 hb k x y, ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ, Matrix.mul_apply]
  calc (∑ z, (shortRingProfile b m W ^ j) x z * shortRingProfile b m W z y)
      ≤ ∑ z, (shortRingProfile b m W ^ j) x z * (1 / (W : ℝ)) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
          (shortRingProfile_le hb0 hb m W z y) (shortRingProfile_pow_nonneg hb0 hb j x z)
    _ = 1 / (W : ℝ) := by
        rw [← Finset.sum_mul, shortRingProfile_pow_rowSum b hm hW, one_mul]

end BlockBand.Native.ErdosRiabov.Kernel
