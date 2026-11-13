module

public import BlockBand.Transmission.LawDuality.RatioMass

/-!
# The eigenvalue form of the ratio duality relation: the pointwise identity

For a chamber point `z = (x, y)` and `t ∈ [0, 1]` put `r_i = (1 + x_it)⁻¹`, `s_j = (1 − y_jt)⁻¹` and
`Λ_z(t) = Σ_i x_ir_i + Σ_j y_js_j` (`dualLam`; minus the eigenvalue gradient of `log F` per unit
weight). **`dual_point`**:
```
t(1−t)Λ_z(t)² = Σ_i [x_i(1+x_i)t r_i² − β^x_i r_i] − Σ_j [y_j(1−y_j)t s_j² + β^y_j s_j].
```
Integrated against `ν = Σ_k t_kδ_{t_k}` the left side is the bracket `Γ(log F)/D₀` of the paper, and
the right side is the part of `𝒟_pF/F` that is linear in `ν` (`DualBracket`).

Proof: all parameters `w ∈ {x_i} ∪ {−y_j}` behave alike. For each pair,
* `(φ(a) − φ(b))/(a − b) = r_ar_b(1 + a + b + abt)`, `φ(w) = w(1+w)r_w` (`pf_diff*`), which turns
  the singular drift sums into pair sums (`two_mul_sum_erase_eq`);
* `t(1−t)(ar_a)(br_b) + r_ar_b(1 + a + b + abt) = 1 + (1−t)(ar_a + br_b)` (`pf_pair*`);
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.LawDuality

variable {p : ℕ}

/-- `Λ_z(t) = Σ_i x_i/(1+x_it) + Σ_j y_j/(1−y_jt)`. -/
def dualLam (z : DualCoord p) (t : ℝ) : ℝ :=
  ∑ i, z.1 i / (1 + z.1 i * t) + ∑ j, z.2 j / (1 - z.2 j * t)

/-- The `ν`-linear part of `𝒟_pF/F` at weight point `t`. -/
def dualPoint (z : DualCoord p) (t : ℝ) : ℝ :=
  ∑ i, (z.1 i * (1 + z.1 i) * t / (1 + z.1 i * t) ^ 2 - dualDriftX z i / (1 + z.1 i * t)) -
    ∑ j, (z.2 j * (1 - z.2 j) * t / (1 - z.2 j * t) ^ 2 + dualDriftY z j / (1 - z.2 j * t))

/-!
## Pair identities
-/

theorem pf_diff {a b t : ℝ} (ha : 1 + a * t ≠ 0) (hb : 1 + b * t ≠ 0) :
    a * (1 + a) / (1 + a * t) - b * (1 + b) / (1 + b * t) =
      (a - b) * ((1 + a + b + a * b * t) / ((1 + a * t) * (1 + b * t))) := by
  set R := 1 + a * t with hR
  set S := 1 + b * t with hS
  field_simp
  rw [hR, hS]; ring

theorem pf_diff_y {a b t : ℝ} (ha : 1 - a * t ≠ 0) (hb : 1 - b * t ≠ 0) :
    a * (1 - a) / (1 - a * t) - b * (1 - b) / (1 - b * t) =
      (a - b) * ((1 - a - b + a * b * t) / ((1 - a * t) * (1 - b * t))) := by
  set R := 1 - a * t with hR
  set S := 1 - b * t with hS
  field_simp
  rw [hR, hS]; ring

theorem pf_diff_xy {a b t : ℝ} (ha : 1 + a * t ≠ 0) (hb : 1 - b * t ≠ 0) :
    a * (1 + a) / (1 + a * t) + b * (1 - b) / (1 - b * t) =
      (a + b) * ((1 + a - b - a * b * t) / ((1 + a * t) * (1 - b * t))) := by
  set R := 1 + a * t with hR
  set S := 1 - b * t with hS
  field_simp
  rw [hR, hS]; ring

theorem pf_pair {a b t : ℝ} (ha : 1 + a * t ≠ 0) (hb : 1 + b * t ≠ 0) :
    t * (1 - t) * (a / (1 + a * t) * (b / (1 + b * t))) +
        (1 + a + b + a * b * t) / ((1 + a * t) * (1 + b * t)) =
      1 + (1 - t) * (a / (1 + a * t)) + (1 - t) * (b / (1 + b * t)) := by
  set R := 1 + a * t with hR
  set S := 1 + b * t with hS
  field_simp
  rw [hR, hS]; ring

theorem pf_pair_y {a b t : ℝ} (ha : 1 - a * t ≠ 0) (hb : 1 - b * t ≠ 0) :
    t * (1 - t) * (a / (1 - a * t) * (b / (1 - b * t))) +
        (1 - a - b + a * b * t) / ((1 - a * t) * (1 - b * t)) =
      1 - (1 - t) * (a / (1 - a * t)) - (1 - t) * (b / (1 - b * t)) := by
  set R := 1 - a * t with hR
  set S := 1 - b * t with hS
  field_simp
  rw [hR, hS]; ring

theorem pf_pair_xy {a b t : ℝ} (ha : 1 + a * t ≠ 0) (hb : 1 - b * t ≠ 0) :
    t * (1 - t) * (a / (1 + a * t) * (b / (1 - b * t))) -
        (1 + a - b - a * b * t) / ((1 + a * t) * (1 - b * t)) =
      -1 - (1 - t) * (a / (1 + a * t)) + (1 - t) * (b / (1 - b * t)) := by
  set R := 1 + a * t with hR
  set S := 1 - b * t with hS
  field_simp
  rw [hR, hS]; ring

theorem pf_diag_x {a t : ℝ} (ha : 1 + a * t ≠ 0) :
    a * (1 + a) * t / (1 + a * t) ^ 2 - (1 + 2 * a) / (1 + a * t) +
      (1 + a + a + a * a * t) / ((1 + a * t) * (1 + a * t)) = 0 := by
  set R := 1 + a * t with hR
  field_simp
  rw [hR]; ring

theorem pf_diag_y {a t : ℝ} (ha : 1 - a * t ≠ 0) :
    a * (1 - a) * t / (1 - a * t) ^ 2 + (1 - 2 * a) / (1 - a * t) -
      (1 - a - a + a * a * t) / ((1 - a * t) * (1 - a * t)) = 0 := by
  set R := 1 - a * t with hR
  field_simp
  rw [hR]; ring

/-- A difference quotient that equals a pair term off the diagonal (and `0/0 = 0` on it). -/
theorem diffQuot_eq {q : ℕ} {g w : Fin q → ℝ} {c : Fin q → Fin q → ℝ} (hw : Function.Injective w)
    (h : ∀ i k, g i - g k = (w i - w k) * c i k) (i k : Fin q) :
    (g i - g k) / (w i - w k) = c i k - if i = k then c i i else 0 := by
  by_cases hik : i = k
  · subst hik; simp
  · have hne : w i - w k ≠ 0 := sub_ne_zero.2 fun he => hik (hw he)
    rw [h, mul_div_cancel_left₀ _ hne]; simp [hik]

theorem sum_sum_diffQuot {q : ℕ} {g w : Fin q → ℝ} {c : Fin q → Fin q → ℝ}
    (hw : Function.Injective w) (h : ∀ i k, g i - g k = (w i - w k) * c i k) :
    ∑ i, ∑ k, (g i - g k) / (w i - w k) = ∑ i, ∑ k, c i k - ∑ i, c i i := by
  simp_rw [diffQuot_eq hw h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem sum_sum_add_const {q : ℕ} (f g : Fin q → ℝ) (c : ℝ) :
    ∑ i, ∑ k, (c + f i + g k) = q * q * c + q * ∑ i, f i + q * ∑ k, g k := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-!
## The identity
-/

/-- **The pointwise eigenvalue form of the ratio duality relation**. -/
theorem dual_point {z : DualCoord p} (hz : z ∈ dualChamber p) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : t * (1 - t) * dualLam z t ^ 2 = dualPoint z t := by
  obtain ⟨hxm, hym, hx0, hy⟩ := hz
  have hd : ∀ i, 1 + z.1 i * t ≠ 0 := fun i => by nlinarith [hx0 i]
  have he : ∀ j, 1 - z.2 j * t ≠ 0 := fun j => by nlinarith [(hy j).1, (hy j).2]
  have hxy : ∀ i j, z.1 i + z.2 j ≠ 0 := fun i j => by linarith [hx0 i, (hy j).1]
  set x := z.1
  set y := z.2
  set u : Fin p → ℝ := fun i => x i / (1 + x i * t)
  set v : Fin p → ℝ := fun j => y j / (1 - y j * t)
  set φ : Fin p → ℝ := fun i => x i * (1 + x i) / (1 + x i * t)
  set ψ : Fin p → ℝ := fun j => y j * (1 - y j) / (1 - y j * t)
  set cxx : Fin p → Fin p → ℝ := fun i k =>
    (1 + x i + x k + x i * x k * t) / ((1 + x i * t) * (1 + x k * t))
  set cyy : Fin p → Fin p → ℝ := fun j l =>
    (1 - y j - y l + y j * y l * t) / ((1 - y j * t) * (1 - y l * t))
  set cxy : Fin p → Fin p → ℝ := fun i j =>
    (1 + x i - y j - x i * y j * t) / ((1 + x i * t) * (1 - y j * t))
  -- the drifts, split into the regular part and the singular sums
  have hbx : ∀ i, dualDriftX z i / (1 + x i * t) = (1 + 2 * x i) / (1 + x i * t) +
      2 * (φ i * ∑ k ∈ Finset.univ.erase i, 1 / (x i - x k)) -
      2 * ∑ j, φ i / (x i + y j) := fun i => by
    have hB : ∑ j, φ i / (x i + y j) = φ i * ∑ j, 1 / (x i + y j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hB, show dualDriftX z i = 1 + 2 * x i + 2 * x i * (1 + x i) *
      ((∑ k ∈ Finset.univ.erase i, 1 / (x i - x k)) - ∑ j, 1 / (x i + y j)) from rfl]
    simp only [φ]
    ring
  have hby : ∀ j, dualDriftY z j / (1 - y j * t) = (1 - 2 * y j) / (1 - y j * t) +
      2 * (ψ j * ∑ l ∈ Finset.univ.erase j, 1 / (y j - y l)) -
      2 * ∑ i, ψ j / (x i + y j) := fun j => by
    have hB : ∑ i, ψ j / (x i + y j) = ψ j * ∑ i, 1 / (x i + y j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hB, show dualDriftY z j = 1 - 2 * y j + 2 * y j * (1 - y j) *
      ((∑ l ∈ Finset.univ.erase j, 1 / (y j - y l)) - ∑ i, 1 / (x i + y j)) from rfl]
    simp only [ψ]
    ring
  have hsx : ∑ i, 2 * (φ i * ∑ k ∈ Finset.univ.erase i, 1 / (x i - x k)) =
      ∑ i, ∑ k, cxx i k - ∑ i, cxx i i := by
    rw [← Finset.mul_sum, two_mul_sum_erase_eq φ x]
    exact sum_sum_diffQuot hxm.injective fun i k => pf_diff (hd i) (hd k)
  have hsy : ∑ j, 2 * (ψ j * ∑ l ∈ Finset.univ.erase j, 1 / (y j - y l)) =
      ∑ j, ∑ l, cyy j l - ∑ j, cyy j j := by
    rw [← Finset.mul_sum, two_mul_sum_erase_eq ψ y]
    exact sum_sum_diffQuot hym.injective fun j l => pf_diff_y (he j) (he l)
  have hm : ∑ i, ∑ j, φ i / (x i + y j) + ∑ j, ∑ i, ψ j / (x i + y j) =
      ∑ i, ∑ j, cxy i j := by
    rw [Finset.sum_comm (f := fun j i => ψ j / (x i + y j)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← add_div, pf_diff_xy (hd i) (he j), mul_div_cancel_left₀ _ (hxy i j)]
  -- diagonal cancellations
  have hgx : ∑ i, (x i * (1 + x i) * t / (1 + x i * t) ^ 2 - (1 + 2 * x i) / (1 + x i * t)) +
      ∑ i, cxx i i = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => pf_diag_x (hd i)
  have hgy : ∑ j, (y j * (1 - y j) * t / (1 - y j * t) ^ 2 + (1 - 2 * y j) / (1 - y j * t)) -
      ∑ j, cyy j j = 0 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun j _ => pf_diag_y (he j)
  -- pair identities
  have hpx : t * (1 - t) * ∑ i, ∑ k, u i * u k + ∑ i, ∑ k, cxx i k =
      p * p * 1 + p * ∑ i, (1 - t) * u i + p * ∑ k, (1 - t) * u k := by
    rw [← sum_sum_add_const, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => pf_pair (hd i) (hd k)
  have hpy : t * (1 - t) * ∑ j, ∑ l, v j * v l + ∑ j, ∑ l, cyy j l =
      p * p * 1 + p * ∑ j, (-(1 - t) * v j) + p * ∑ l, (-(1 - t) * v l) := by
    rw [← sum_sum_add_const, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [pf_pair_y (he j) (he l)]; ring
  have hpm : t * (1 - t) * ∑ i, ∑ j, u i * v j - ∑ i, ∑ j, cxy i j =
      p * p * (-1) + p * ∑ i, (-(1 - t) * u i) + p * ∑ j, ((1 - t) * v j) := by
    rw [← sum_sum_add_const, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pf_pair_xy (hd i) (he j)]; ring
  -- assemble
  have hL : dualLam z t ^ 2 = ∑ i, ∑ k, u i * u k + 2 * ∑ i, ∑ j, u i * v j +
      ∑ j, ∑ l, v j * v l := by
    rw [show dualLam z t = ∑ i, u i + ∑ j, v j from rfl, add_sq, sq, sq, mul_assoc 2,
      Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum]
  have hP : dualPoint z t =
      ∑ i, (x i * (1 + x i) * t / (1 + x i * t) ^ 2 - (1 + 2 * x i) / (1 + x i * t)) -
        (∑ i, ∑ k, cxx i k - ∑ i, cxx i i) + 2 * ∑ i, ∑ j, φ i / (x i + y j) -
      (∑ j, (y j * (1 - y j) * t / (1 - y j * t) ^ 2 + (1 - 2 * y j) / (1 - y j * t)) +
        (∑ j, ∑ l, cyy j l - ∑ j, cyy j j) - 2 * ∑ j, ∑ i, ψ j / (x i + y j)) := by
    have h1 : ∑ i, (x i * (1 + x i) * t / (1 + x i * t) ^ 2 - dualDriftX z i / (1 + x i * t)) =
        ∑ i, (x i * (1 + x i) * t / (1 + x i * t) ^ 2 - (1 + 2 * x i) / (1 + x i * t)) -
          ∑ i, 2 * (φ i * ∑ k ∈ Finset.univ.erase i, 1 / (x i - x k)) +
          2 * ∑ i, ∑ j, φ i / (x i + y j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hbx i]; ring
    have h2 : ∑ j, (y j * (1 - y j) * t / (1 - y j * t) ^ 2 + dualDriftY z j / (1 - y j * t)) =
        ∑ j, (y j * (1 - y j) * t / (1 - y j * t) ^ 2 + (1 - 2 * y j) / (1 - y j * t)) +
          ∑ j, 2 * (ψ j * ∑ l ∈ Finset.univ.erase j, 1 / (y j - y l)) -
          2 * ∑ j, ∑ i, ψ j / (x i + y j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hby j]; ring
    rw [show dualPoint z t =
      ∑ i, (x i * (1 + x i) * t / (1 + x i * t) ^ 2 - dualDriftX z i / (1 + x i * t)) -
        ∑ j, (y j * (1 - y j) * t / (1 - y j * t) ^ 2 + dualDriftY z j / (1 - y j * t)) from rfl,
      h1, h2, hsx, hsy]
  rw [hL, hP]
  have hU : ∀ c : ℝ, ∑ i, c * u i = c * ∑ i, u i := fun c => (Finset.mul_sum _ _ _).symm
  have hV : ∀ c : ℝ, ∑ j, c * v j = c * ∑ j, v j := fun c => (Finset.mul_sum _ _ _).symm
  rw [hU] at hpx
  rw [hV] at hpy
  rw [hU, hV] at hpm
  linear_combination hpx + hpy + 2 * hpm - hgx + hgy - 2 * hm

end BlockBand.Transmission.LawForced
