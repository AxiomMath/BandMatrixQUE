module

public import BlockBand.Palm.MomentFlow.MaxStep

/-!
# The averaged identity for the flattened flow, with the dyadic-shell ramp bound

`kerAt λ h i j = N⁻¹ h/((λ_j - λ_i)² + h²)` is the resolvent kernel at height `h` (so
`remKernel F a ω s i j η = kerAt (λ(s)) η i j` definitionally).

* `remSum_add`, `remSum_one`: additivity and `remSum K 1 = Σ_j K_ij + Σ_j K_ij ξ_j - K_ii`.
* `r3_split`: with `Av F(ζ) = a_ζ F(ζ) + 1 - a_ζ`,
  `remSum K (Av F) = a_ξ remSum K F + (1-a_ξ) remSum K 1 + Σ_j K coef (a_{t_j} - a_ξ)(F(t_j) - 1)`.
* `kerAt_shell`: the pointwise dyadic-shell inequality
  `K^η(d) min(1, β(d+η)) ≤ 16βη Σ_{k≤L} K^{2^kη}(d) + (2η/(2^Lη)) K^{2^Lη}(d)`.
* `ramp_pullout`: summed against `remCoef · (F + 1)`, the ramp pull-out costs
  `(16βη(L+1) + 2η/(2^Lη)) (B_F + B_1)`, where `B_F`, `B_1` bound `remSum K^{2^kη} F` and
  `remSum K^{2^kη} 1` for `k ≤ L` (from the removal identity and the averaged law at those
  heights). With `β = 2C N/w` (ramp Lipschitz `2/w` times the local count
  `labelDist ≤ C N(d + η)`) and `L ≈ log₂(1/η)` this is the bound `C(Nη/w) log N`.
* **`r3_bound`**: `|remSum K g ξ i - V(a_ξ Ψ + 1 - a_ξ)| ≤ e_R + (E₂ + r Kmax) +
  (16βη(L+1) + 2η/(2^Lη))(B_F + B_1) + (V + E₂ + r Kmax) δ_g`, where
  `|remSum K F ξ i - VΨ| ≤ e_R` (removal identity), `|Σ_j K_ij - V| ≤ E₂` (averaged law), and
  `|g(ζ) - Av F(ζ)| ≤ δ_g` at every target (long-short comparison and commutator).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- The resolvent kernel `N⁻¹ h/((λ_j - λ_i)² + h²)` at height `h`. -/
def kerAt (lam : Fin N → ℝ) (h : ℝ) (i j : Fin N) : ℝ :=
  (N : ℝ)⁻¹ * (h / ((lam j - lam i) ^ 2 + h ^ 2))

theorem kerAt_nonneg (lam : Fin N → ℝ) {h : ℝ} (hh : 0 ≤ h) (i j : Fin N) :
    0 ≤ kerAt lam h i j := by
  unfold kerAt; positivity

theorem kerAt_le (lam : Fin N → ℝ) {h : ℝ} (hh : 0 < h) (i j : Fin N) :
    kerAt lam h i j ≤ ((N : ℝ) * h)⁻¹ := by
  unfold kerAt
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp
  have hN : (0 : ℝ) < N := by exact_mod_cast h0
  rw [mul_inv, div_eq_mul_inv]
  have : h * ((lam j - lam i) ^ 2 + h ^ 2)⁻¹ ≤ h⁻¹ := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have : h⁻¹ * h = 1 := inv_mul_cancel₀ hh.ne'
    nlinarith [sq_nonneg (lam j - lam i), inv_pos.2 hh]
  exact mul_le_mul_of_nonneg_left this (by positivity)

theorem remCoef_nonneg (ξ : Occ N) (i j : Fin N) : 0 ≤ remCoef ξ i j := by
  unfold remCoef; split_ifs <;> positivity

theorem remCoef_le {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) (i j : Fin N) :
    remCoef ξ i j ≤ (r : ℝ) + 1 := by
  have hξj : ∀ j, (ξ j : ℝ) ≤ r := by
    intro j
    have h := hξ
    rw [mem_sector] at h
    have : ξ j ≤ r := h ▸ Finset.single_le_sum (fun k _ => Nat.zero_le (ξ k)) (mem_univ j)
    exact_mod_cast this
  unfold remCoef; split_ifs
  · linarith [hξj i]
  · linarith [hξj j]

theorem remSum_add (K : Fin N → Fin N → ℝ) (f g : Occ N → ℝ) (ξ : Occ N) (i : Fin N) :
    remSum K (fun ζ => f ζ + g ζ) ξ i = remSum K f ξ i + remSum K g ξ i := by
  unfold remSum; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring

/-- `remSum K 1 = Σ_j K_ij + Σ_j K_ij ξ_j - K_ii`. -/
theorem remSum_one (K : Fin N → Fin N → ℝ) (ξ : Occ N) (i : Fin N) :
    remSum K (fun _ => 1) ξ i = ∑ j, K i j + ∑ j, K i j * (ξ j : ℝ) - K i i := by
  rw [remSum_split, sum_erase_add_diag K i,
    ← Finset.add_sum_erase _ (fun j => K i j * (ξ j : ℝ)) (mem_univ i)]
  have : ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) * 1 =
      ∑ j ∈ univ.erase i, K i j + ∑ j ∈ univ.erase i, K i j * (ξ j : ℝ) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]; ring

/-- `|remSum K 1 - Σ_j K_ij| ≤ r Kmax` at an occupied label. -/
theorem remSum_one_sub_le {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) {K : Fin N → Fin N → ℝ}
    {Kmax : ℝ} (hK : ∀ i j, 0 ≤ K i j) (hKm : ∀ i j, K i j ≤ Kmax) {i : Fin N} (hi : 0 < ξ i) :
    |remSum K (fun _ => 1) ξ i - ∑ j, K i j| ≤ r * Kmax := by
  rw [remSum_one]
  have hr : (r : ℝ) = ∑ j, (ξ j : ℝ) := by
    have h := hξ; rw [mem_sector] at h; exact_mod_cast h.symm
  have h1 : ∑ j, K i j * (ξ j : ℝ) ≤ r * Kmax := by
    rw [hr, Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hKm i j) (by positivity)
  have h2 : K i i ≤ ∑ j, K i j * (ξ j : ℝ) := by
    have hxi : (1 : ℝ) ≤ ξ i := by exact_mod_cast hi
    calc K i i ≤ K i i * (ξ i : ℝ) := by nlinarith [hK i i]
      _ ≤ ∑ j, K i j * (ξ j : ℝ) :=
        Finset.single_le_sum (f := fun j => K i j * (ξ j : ℝ))
          (fun j _ => mul_nonneg (hK i j) (by positivity)) (mem_univ i)
  rw [abs_le]; constructor <;> nlinarith [hK i i]

/-- The flattening `Av F(ζ) = a_ζ F(ζ) + (1 - a_ζ)`. -/
def avFlat (aR : Occ N → ℝ) (f : Occ N → ℝ) (ζ : Occ N) : ℝ := aR ζ * f ζ + (1 - aR ζ)

/-- Algebraic split of the restored sum of the flattened data. -/
theorem r3_split (K : Fin N → Fin N → ℝ) (aR f : Occ N → ℝ) (ξ : Occ N) (i : Fin N) :
    remSum K (avFlat aR f) ξ i = aR ξ * remSum K f ξ i + (1 - aR ξ) * remSum K (fun _ => 1) ξ i +
      ∑ j, K i j * remCoef ξ i j * ((aR (remTarget ξ i j) - aR ξ) * (f (remTarget ξ i j) - 1)) := by
  unfold remSum avFlat
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Kernel comparison across heights: if `d² + h² ≤ M(d² + η²)` then `K^η ≤ (Mη/h) K^h`. -/
theorem kerAt_le_scale (lam : Fin N → ℝ) {η h M : ℝ} (hη : 0 < η) (hh : 0 < h) (i j : Fin N)
    (hM : (lam j - lam i) ^ 2 + h ^ 2 ≤ M * ((lam j - lam i) ^ 2 + η ^ 2)) :
    kerAt lam η i j ≤ M * η / h * kerAt lam h i j := by
  unfold kerAt
  set x := (lam j - lam i) ^ 2
  have hx : 0 ≤ x := sq_nonneg _
  have e : M * η / h * ((N : ℝ)⁻¹ * (h / (x + h ^ 2))) = (N : ℝ)⁻¹ * (M * η / (x + h ^ 2)) := by
    field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Pointwise dyadic-shell inequality.** -/
theorem kerAt_shell (lam : Fin N → ℝ) {η β : ℝ} (hη : 0 < η) (hβ : 0 ≤ β) (L : ℕ)
    (i j : Fin N) :
    kerAt lam η i j * min 1 (β * (|lam j - lam i| + η)) ≤
      16 * β * η * ∑ k ∈ range (L + 1), kerAt lam (2 ^ k * η) i j +
        2 * η / (2 ^ L * η) * kerAt lam (2 ^ L * η) i j := by
  set d := |lam j - lam i| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hsq : (lam j - lam i) ^ 2 = d ^ 2 := (sq_abs _).symm
  have hterm : ∀ k, 0 ≤ kerAt lam (2 ^ k * η) i j := fun k => kerAt_nonneg lam (by positivity) i j
  have hsum0 : 0 ≤ ∑ k ∈ range (L + 1), kerAt lam (2 ^ k * η) i j :=
    Finset.sum_nonneg fun k _ => hterm k
  have hmin0 : 0 ≤ min 1 (β * (d + η)) := le_min zero_le_one (by positivity)
  have hmin1 : min 1 (β * (d + η)) ≤ 1 := min_le_left _ _
  have hmin2 : min 1 (β * (d + η)) ≤ β * (d + η) := min_le_right _ _
  have hK0 := kerAt_nonneg lam hη.le i j
  by_cases hfar : 2 ^ L * η ≤ d
  · have hL : 0 < 2 ^ L * η := by positivity
    have hk : kerAt lam η i j ≤ 2 * η / (2 ^ L * η) * kerAt lam (2 ^ L * η) i j := by
      refine kerAt_le_scale lam hη hL i j ?_
      rw [hsq]; nlinarith
    have h1 : kerAt lam η i j * min 1 (β * (d + η)) ≤ kerAt lam η i j :=
      mul_le_of_le_one_right hK0 hmin1
    have : 0 ≤ 16 * β * η * ∑ k ∈ range (L + 1), kerAt lam (2 ^ k * η) i j := by positivity
    linarith
  · push Not at hfar
    have hex : ∃ k, d < 2 ^ k * η := ⟨L, hfar⟩
    set k := Nat.find hex
    have hk : d < 2 ^ k * η := Nat.find_spec hex
    have hkL : k ≤ L := Nat.find_min' hex hfar
    have hkpos : 0 < 2 ^ k * η := by positivity
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hshell : kerAt lam η i j ≤ 8 * η / (2 ^ k * η) * kerAt lam (2 ^ k * η) i j := by
      refine kerAt_le_scale lam hη hkpos i j ?_
      rw [hsq]
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0]; simp only [pow_zero, one_mul]; nlinarith [sq_nonneg d, sq_nonneg η]
      · have hk1 : ¬ d < 2 ^ (k - 1) * η := Nat.find_min hex (by omega)
        push Not at hk1
        have hpow : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
          rw [← pow_succ']; congr 1; omega
        have hd2 : (2 ^ k * η) ^ 2 ≤ 4 * d ^ 2 := by
          have h0 : 0 ≤ (2 : ℝ) ^ (k - 1) * η := by positivity
          have := mul_le_mul hk1 hk1 h0 hd0
          rw [hpow]
          calc (2 * 2 ^ (k - 1) * η) ^ 2 = 4 * ((2 ^ (k - 1) * η) * (2 ^ (k - 1) * η)) := by ring
            _ ≤ 4 * (d * d) := by linarith
            _ = 4 * d ^ 2 := by ring
        nlinarith [sq_nonneg d, sq_nonneg η]
    have hw : min 1 (β * (d + η)) ≤ 2 * β * (2 ^ k * η) := by
      refine hmin2.trans ?_
      have : η ≤ 2 ^ k * η := le_mul_of_one_le_left hη.le (one_le_pow₀ (by norm_num))
      nlinarith
    have hmem : k ∈ range (L + 1) := mem_range.2 (by omega)
    have hone : kerAt lam (2 ^ k * η) i j ≤ ∑ k ∈ range (L + 1), kerAt lam (2 ^ k * η) i j :=
      Finset.single_le_sum (f := fun k => kerAt lam (2 ^ k * η) i j) (fun k _ => hterm k) hmem
    have hc0 : 0 ≤ 8 * η / (2 ^ k * η) * kerAt lam (2 ^ k * η) i j := by
      have := hterm k; positivity
    calc kerAt lam η i j * min 1 (β * (d + η))
        ≤ (8 * η / (2 ^ k * η) * kerAt lam (2 ^ k * η) i j) * (2 * β * (2 ^ k * η)) :=
          mul_le_mul hshell hw hmin0 hc0
      _ = 16 * β * η * kerAt lam (2 ^ k * η) i j := by
          field_simp
          ring
      _ ≤ 16 * β * η * ∑ k ∈ range (L + 1), kerAt lam (2 ^ k * η) i j := by
          gcongr
      _ ≤ _ := by
          have : 0 ≤ 2 * η / (2 ^ L * η) * kerAt lam (2 ^ L * η) i j := by
            have := hterm L; positivity
          linarith

/-- **Ramp pull-out by dyadic shells.** -/
theorem ramp_pullout {ξ : Occ N} (i : Fin N) (lam : Fin N → ℝ)
    {η β BF B1 : ℝ} (hη : 0 < η) (hβ : 0 ≤ β) (L : ℕ) (aR f : Occ N → ℝ)
    (hf0 : ∀ j, 0 ≤ f (remTarget ξ i j))
    (hlip : ∀ j, |aR (remTarget ξ i j) - aR ξ| ≤ min 1 (β * (|lam j - lam i| + η)))
    (hBF : ∀ k ≤ L, remSum (kerAt lam (2 ^ k * η)) f ξ i ≤ BF)
    (hB1 : ∀ k ≤ L, remSum (kerAt lam (2 ^ k * η)) (fun _ => 1) ξ i ≤ B1) :
    |∑ j, kerAt lam η i j * remCoef ξ i j *
        ((aR (remTarget ξ i j) - aR ξ) * (f (remTarget ξ i j) - 1))| ≤
      (16 * β * η * (L + 1) + 2 * η / (2 ^ L * η)) * (BF + B1) := by
  set W : ℝ → Fin N → ℝ := fun h j => kerAt lam h i j * remCoef ξ i j * (f (remTarget ξ i j) + 1)
  have hW0 : ∀ h, 0 ≤ h → ∀ j, 0 ≤ W h j := fun h hh j =>
    mul_nonneg (mul_nonneg (kerAt_nonneg lam hh i j) (remCoef_nonneg ξ i j)) (by linarith [hf0 j])
  have hWs : ∀ k ≤ L, ∑ j, W (2 ^ k * η) j ≤ BF + B1 := by
    intro k hk
    have : ∑ j, W (2 ^ k * η) j = remSum (kerAt lam (2 ^ k * η)) f ξ i +
        remSum (kerAt lam (2 ^ k * η)) (fun _ => 1) ξ i := by
      unfold remSum; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [W]; ring
    rw [this]; linarith [hBF k hk, hB1 k hk]
  have hpt : ∀ j, |kerAt lam η i j * remCoef ξ i j *
      ((aR (remTarget ξ i j) - aR ξ) * (f (remTarget ξ i j) - 1))| ≤
      16 * β * η * ∑ k ∈ range (L + 1), W (2 ^ k * η) j + 2 * η / (2 ^ L * η) * W (2 ^ L * η) j := by
    intro j
    have hc := remCoef_nonneg ξ i j
    have hK := kerAt_nonneg lam hη.le i j
    have hfa : |f (remTarget ξ i j) - 1| ≤ f (remTarget ξ i j) + 1 := by
      rw [abs_le]; constructor <;> linarith [hf0 j]
    have hsh := kerAt_shell lam hη hβ L i j
    have hf1 : 0 ≤ remCoef ξ i j * (f (remTarget ξ i j) + 1) := mul_nonneg hc (by linarith [hf0 j])
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hK, abs_of_nonneg hc]
    calc kerAt lam η i j * remCoef ξ i j *
          (|aR (remTarget ξ i j) - aR ξ| * |f (remTarget ξ i j) - 1|)
        ≤ kerAt lam η i j * remCoef ξ i j *
          (min 1 (β * (|lam j - lam i| + η)) * (f (remTarget ξ i j) + 1)) := by
          gcongr
          · exact hlip j
      _ = (kerAt lam η i j * min 1 (β * (|lam j - lam i| + η))) *
          (remCoef ξ i j * (f (remTarget ξ i j) + 1)) := by ring
      _ ≤ (16 * β * η * ∑ k ∈ range (L + 1), kerAt lam (2 ^ k * η) i j +
            2 * η / (2 ^ L * η) * kerAt lam (2 ^ L * η) i j) *
          (remCoef ξ i j * (f (remTarget ξ i j) + 1)) := mul_le_mul_of_nonneg_right hsh hf1
      _ = _ := by
          simp only [W]
          rw [add_mul, mul_assoc (16 * β * η), Finset.sum_mul]
          congr 1
          · congr 1; exact Finset.sum_congr rfl fun k _ => by ring
          · ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => hpt j).trans ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_comm (s := (univ : Finset (Fin N)))]
  have hS : ∑ k ∈ range (L + 1), ∑ j, W (2 ^ k * η) j ≤ (L + 1) * (BF + B1) := by
    calc ∑ k ∈ range (L + 1), ∑ j, W (2 ^ k * η) j ≤ ∑ k ∈ range (L + 1), (BF + B1) :=
          Finset.sum_le_sum fun k hk => hWs k (by have := mem_range.1 hk; omega)
      _ = (L + 1) * (BF + B1) := by simp; ring
  have hLs := hWs L le_rfl
  have hc1 : 0 ≤ 16 * β * η := by positivity
  have hc2 : 0 ≤ 2 * η / (2 ^ L * η) := by positivity
  calc 16 * β * η * ∑ k ∈ range (L + 1), ∑ j, W (2 ^ k * η) j +
        2 * η / (2 ^ L * η) * ∑ j, W (2 ^ L * η) j
      ≤ 16 * β * η * ((L + 1) * (BF + B1)) + 2 * η / (2 ^ L * η) * (BF + B1) := by
        gcongr
    _ = _ := by ring

/-- **The averaged identity for the flattened flow at one time.** -/
theorem r3_bound {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) {i : Fin N} (hi : 0 < ξ i)
    (lam : Fin N → ℝ) {η β BF B1 V Ψ eR2 E₂ δg : ℝ} (hη : 0 < η) (hβ : 0 ≤ β) (L : ℕ)
    (aR F g : Occ N → ℝ) (haR : 0 ≤ aR ξ ∧ aR ξ ≤ 1)
    (hF0 : ∀ j, 0 ≤ F (remTarget ξ i j))
    (hlip : ∀ j, |aR (remTarget ξ i j) - aR ξ| ≤ min 1 (β * (|lam j - lam i| + η)))
    (hBF : ∀ k ≤ L, remSum (kerAt lam (2 ^ k * η)) F ξ i ≤ BF)
    (hB1 : ∀ k ≤ L, remSum (kerAt lam (2 ^ k * η)) (fun _ => 1) ξ i ≤ B1)
    (hR2 : |remSum (kerAt lam η) F ξ i - V * Ψ| ≤ eR2)
    (hAv : |∑ j, kerAt lam η i j - V| ≤ E₂)
    (hg : ∀ j, |g (remTarget ξ i j) - avFlat aR F (remTarget ξ i j)| ≤ δg) :
    |remSum (kerAt lam η) g ξ i - V * (aR ξ * Ψ + (1 - aR ξ))| ≤
      eR2 + (E₂ + r * ((N : ℝ) * η)⁻¹) +
        (16 * β * η * (L + 1) + 2 * η / (2 ^ L * η)) * (BF + B1) +
        (V + E₂ + r * ((N : ℝ) * η)⁻¹) * δg := by
  set K := kerAt lam η
  set Kmax := ((N : ℝ) * η)⁻¹
  have hK : ∀ i j, 0 ≤ K i j := fun i j => kerAt_nonneg lam hη.le i j
  have hKm : ∀ i j, K i j ≤ Kmax := fun i j => kerAt_le lam hη i j
  have h1 := remSum_one_sub_le hξ hK hKm hi
  have hdec : remSum K g ξ i = remSum K (avFlat aR F) ξ i +
      remSum K (fun ζ => g ζ - avFlat aR F ζ) ξ i := by
    rw [← remSum_add]; congr 1; funext ζ; ring
  have hdiff : |remSum K (fun ζ => g ζ - avFlat aR F ζ) ξ i| ≤ (V + E₂ + r * Kmax) * δg := by
    have hδ : 0 ≤ δg := (abs_nonneg _).trans (hg i)
    have hsum : |remSum K (fun ζ => g ζ - avFlat aR F ζ) ξ i| ≤
        δg * remSum K (fun _ => 1) ξ i := by
      unfold remSum
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hK i j) (remCoef_nonneg ξ i j)), mul_one]
      have := mul_le_mul_of_nonneg_left (hg j) (mul_nonneg (hK i j) (remCoef_nonneg ξ i j))
      linarith
    have h2 : remSum K (fun _ => 1) ξ i ≤ V + E₂ + r * Kmax := by
      have := (abs_le.1 h1).2; have := (abs_le.1 hAv).2; linarith
    calc _ ≤ δg * remSum K (fun _ => 1) ξ i := hsum
      _ ≤ δg * (V + E₂ + r * Kmax) := mul_le_mul_of_nonneg_left h2 hδ
      _ = _ := by ring
  have hshell := ramp_pullout i lam hη hβ L aR F hF0 hlip hBF hB1
  have hsplit := r3_split K aR F ξ i
  have he0 : 0 ≤ eR2 := (abs_nonneg _).trans hR2
  have hone : |remSum K (fun _ => 1) ξ i - V| ≤ E₂ + r * Kmax := by
    calc |remSum K (fun _ => 1) ξ i - V| =
          |(remSum K (fun _ => 1) ξ i - ∑ j, K i j) + (∑ j, K i j - V)| := by ring_nf
      _ ≤ |remSum K (fun _ => 1) ξ i - ∑ j, K i j| + |∑ j, K i j - V| := abs_add_le _ _
      _ ≤ r * Kmax + E₂ := add_le_add h1 hAv
      _ = E₂ + r * Kmax := by ring
  have hmain : remSum K g ξ i - V * (aR ξ * Ψ + (1 - aR ξ)) =
      aR ξ * (remSum K F ξ i - V * Ψ) + (1 - aR ξ) * (remSum K (fun _ => 1) ξ i - V) +
      (∑ j, K i j * remCoef ξ i j * ((aR (remTarget ξ i j) - aR ξ) * (F (remTarget ξ i j) - 1))) +
      remSum K (fun ζ => g ζ - avFlat aR F ζ) ξ i := by
    rw [hdec, hsplit]; ring
  rw [hmain]
  have t1 : |aR ξ * (remSum K F ξ i - V * Ψ)| ≤ eR2 := by
    rw [abs_mul, abs_of_nonneg haR.1]
    calc aR ξ * |remSum K F ξ i - V * Ψ| ≤ 1 * eR2 := mul_le_mul haR.2 hR2 (abs_nonneg _) zero_le_one
      _ = eR2 := one_mul _
  have t2 : |(1 - aR ξ) * (remSum K (fun _ => 1) ξ i - V)| ≤ E₂ + r * Kmax := by
    rw [abs_mul, abs_of_nonneg (by linarith [haR.2])]
    have h0 : 0 ≤ E₂ + r * Kmax := (abs_nonneg _).trans hone
    calc (1 - aR ξ) * |remSum K (fun _ => 1) ξ i - V| ≤ 1 * (E₂ + r * Kmax) :=
          mul_le_mul (by linarith [haR.1]) hone (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  calc _ ≤ |aR ξ * (remSum K F ξ i - V * Ψ)| + |(1 - aR ξ) * (remSum K (fun _ => 1) ξ i - V)| +
        |∑ j, K i j * remCoef ξ i j * ((aR (remTarget ξ i j) - aR ξ) * (F (remTarget ξ i j) - 1))| +
        |remSum K (fun ζ => g ζ - avFlat aR F ζ) ξ i| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by gcongr

end BlockBand.Palm.MomentFlow
