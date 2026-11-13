module

public import BlockBand.Palm.MomentFlow.Generator
public import BlockBand.Palm.RelativeLocalizationTrunc
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# `r`-particle finite speed, deterministic layer: the product weight and its drift

Everything is at one time and one eigenvalue vector `λ`; no measure.

* `cfgWeight φ λ ξ = ∏_m φ(λ_m)^{ξ_m}` (product weight on configurations). Moving a particle
  from `i` to `j` multiplies it by `φ(λ_j)/φ(λ_i)`: `cfgWeight_move`, `cfgWeight_eq_mul_remove`.
* `cfgRate N λ ℓ g`: short rates `1[i≠j, |i-j|<ℓ] / (N max((λ_i-λ_j)², g²))`; `g = 0` gives
  the exact short couplings `c_ij`, and `cfgRate_eq_zero_gap` identifies the truncated rates
  with the exact ones when all gaps are `≥ g`.
* `cfgD1`, `cfgD2`: the first and second `λ_i`-derivatives of the weight.
* `cfg_point_drift_le` (**drift cancellation, per configuration**): with exact short rates,
  `𝓢W(ξ) + Σ_i (D_i ∂_iW(ξ) + ∂²_iW(ξ)/(2N)) ≤ κ_r W(ξ)` on the `r`-particle sector, with
  `κ_r = r κ₁ + r² A²(K²+1)/(2N)`, `κ₁` the one-particle rate of `label_drift_le`.
  Proof: since `jumpCoeff = ξ_i + ξ_iξ_j`, the `ξ_i` part is `Σ_i ξ_i W(ξ-δ_i)` times the
  one-particle bracket of `label_drift_le` (the linear Taylor term cancels the Dyson drift); the
  `ξ_iξ_j` part symmetrizes to `½ Σ c_ij ξ_iξ_j W(ξ-δ_i-δ_j) (φ_j-φ_i)²`, of second order by
  the mean value theorem; the extra Itô term `ξ_i(ξ_i-1) φ'_i² W(ξ-2δ_i)/(2N)` is second order.
* `cfg_drift_le` (**summed form**): by the counting-measure self-adjointness of the moment
  generator, for `v ≥ 0` on the sector,
  `Σ_ξ W(ξ) (𝓢 v)(ξ) + Σ_ξ v(ξ) Σ_i (D_i ∂_iW + ∂²_iW/(2N)) ≤ κ_r Σ_ξ W(ξ) v(ξ)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization

variable {N : ℕ}

/-!
### The product weight
-/

/-- `W_φ(λ, ξ) = ∏_m φ(λ_m)^{ξ_m}`. -/
def cfgWeight (φ : ℝ → ℝ) (lam : Fin N → ℝ) (ξ : Occ N) : ℝ := ∏ m, φ (lam m) ^ ξ m

theorem cfgWeight_nonneg {φ : ℝ → ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (lam : Fin N → ℝ) (ξ : Occ N) :
    0 ≤ cfgWeight φ lam ξ :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (hφ0 _) _

theorem cfgWeight_le_pow {φ : ℝ → ℝ} {M : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hφM : ∀ z, φ z ≤ M)
    (lam : Fin N → ℝ) {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) :
    cfgWeight φ lam ξ ≤ M ^ r := by
  rw [← mem_sector.1 hξ, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (hφ0 _) _)
    fun m _ => pow_le_pow_left₀ (hφ0 _) (hφM _) _

theorem cfgWeight_split (φ : ℝ → ℝ) (lam : Fin N → ℝ) (ξ : Occ N) (j : Fin N) :
    cfgWeight φ lam ξ = φ (lam j) ^ ξ j * ∏ m ∈ univ.erase j, φ (lam m) ^ ξ m := by
  unfold cfgWeight
  rw [← Finset.mul_prod_erase _ _ (mem_univ j)]

theorem cfgWeight_update (φ : ℝ → ℝ) (lam : Fin N → ℝ) (ξ : Occ N) (j : Fin N) (n : ℕ) :
    cfgWeight φ lam (Function.update ξ j n) =
      φ (lam j) ^ n * ∏ m ∈ univ.erase j, φ (lam m) ^ ξ m := by
  rw [cfgWeight_split φ lam _ j]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (mem_erase.1 hk).1]

theorem cfgWeight_update_succ (φ : ℝ → ℝ) (lam : Fin N → ℝ) (ξ : Occ N) (j : Fin N) :
    cfgWeight φ lam (Function.update ξ j (ξ j + 1)) = φ (lam j) * cfgWeight φ lam ξ := by
  rw [cfgWeight_update, cfgWeight_split φ lam ξ j, pow_succ]
  ring

theorem remove_apply_self (ξ : Occ N) (i : Fin N) : remove ξ i i = ξ i - 1 := by
  simp [remove]

theorem remove_apply_of_ne (ξ : Occ N) {i k : Fin N} (h : k ≠ i) : remove ξ i k = ξ k := by
  simp [remove, h]

theorem update_remove_succ (ξ : Occ N) {i : Fin N} (hi : 0 < ξ i) :
    Function.update (remove ξ i) i (remove ξ i i + 1) = ξ := by
  funext k
  by_cases hk : k = i
  · subst hk; simp only [Function.update_self, remove_apply_self]; omega
  · rw [Function.update_of_ne hk, remove_apply_of_ne ξ hk]

theorem remove_comm (ξ : Occ N) {i j : Fin N} (hij : i ≠ j) :
    remove (remove ξ i) j = remove (remove ξ j) i := by
  funext k
  by_cases hki : k = i
  · subst hki
    rw [remove_apply_of_ne _ hij, remove_apply_self, remove_apply_self, remove_apply_of_ne _ hij]
  · by_cases hkj : k = j
    · subst hkj
      rw [remove_apply_self, remove_apply_of_ne _ hki, remove_apply_of_ne _ hki,
        remove_apply_self]
    · rw [remove_apply_of_ne _ hkj, remove_apply_of_ne _ hki, remove_apply_of_ne _ hki,
        remove_apply_of_ne _ hkj]

/-- `W(ξ) = φ(λ_i) W(ξ - δ_i)` when `i` is occupied. -/
theorem cfgWeight_eq_mul_remove (φ : ℝ → ℝ) (lam : Fin N → ℝ) (ξ : Occ N) {i : Fin N}
    (hi : 0 < ξ i) : cfgWeight φ lam ξ = φ (lam i) * cfgWeight φ lam (remove ξ i) := by
  conv_lhs => rw [← update_remove_succ ξ hi]
  exact cfgWeight_update_succ φ lam _ i

/-- `W(ξ^{i,j}) = φ(λ_j) W(ξ - δ_i)`. -/
theorem cfgWeight_move (φ : ℝ → ℝ) (lam : Fin N → ℝ) (ξ : Occ N) {i j : Fin N} (hij : i ≠ j) :
    cfgWeight φ lam (move ξ i j) = φ (lam j) * cfgWeight φ lam (remove ξ i) := by
  rw [move_eq_update_remove]
  have h : remove ξ i j = ξ j := remove_apply_of_ne ξ (Ne.symm hij)
  rw [← h]
  exact cfgWeight_update_succ φ lam _ j

/-- `ξ_i W(ξ - δ_i) φ(λ_i) = ξ_i W(ξ)` (both sides vanish if `i` is empty). -/
theorem cast_mul_cfgWeight_remove (φ : ℝ → ℝ) (lam : Fin N → ℝ) (ξ : Occ N) (i : Fin N) :
    (ξ i : ℝ) * cfgWeight φ lam (remove ξ i) * φ (lam i) = (ξ i : ℝ) * cfgWeight φ lam ξ := by
  rcases Nat.eq_zero_or_pos (ξ i) with hi | hi
  · simp [hi]
  · rw [cfgWeight_eq_mul_remove φ lam ξ hi]; ring

/-!
### Short rates
-/

/-- Short rates, truncated at gap `g`: `1[i ≠ j, |i-j| < ℓ] / (N max((λ_i - λ_j)², g²))`. -/
def cfgRate (N : ℕ) (lam : Fin N → ℝ) (ℓ : ℕ) (g : ℝ) (i j : Fin N) : ℝ := by
  classical
  exact if i ≠ j ∧ labelDist i j < ℓ then truncRate N g (lam i - lam j) else 0

theorem truncRate_nonneg' (g x : ℝ) : 0 ≤ truncRate N g x := by
  unfold truncRate
  have : 0 ≤ max (x ^ 2) (g ^ 2) := le_max_of_le_left (sq_nonneg x)
  positivity

theorem cfgRate_nonneg (lam : Fin N → ℝ) (ℓ : ℕ) (g : ℝ) (i j : Fin N) :
    0 ≤ cfgRate N lam ℓ g i j := by
  unfold cfgRate; split_ifs
  · exact truncRate_nonneg' _ _
  · exact le_rfl

theorem cfgRate_symm (lam : Fin N → ℝ) (ℓ : ℕ) (g : ℝ) (i j : Fin N) :
    cfgRate N lam ℓ g i j = cfgRate N lam ℓ g j i := by
  unfold cfgRate
  have hd : labelDist i j = labelDist j i := labelDist_symm i j
  have hr : truncRate N g (lam i - lam j) = truncRate N g (lam j - lam i) := by
    unfold truncRate; congr 3; ring
  by_cases h : i ≠ j ∧ labelDist i j < ℓ
  · have h' : j ≠ i ∧ labelDist j i < ℓ := ⟨Ne.symm h.1, hd ▸ h.2⟩
    rw [ite_eq_left h, ite_eq_left h', hr]
  · have h' : ¬ (j ≠ i ∧ labelDist j i < ℓ) := fun h' => h ⟨Ne.symm h'.1, hd.symm ▸ h'.2⟩
    rw [ite_eq_right h, ite_eq_right h']

/-- With all gaps `≥ g ≥ 0`, the truncated short rates are the exact ones. -/
theorem cfgRate_eq_zero_gap {lam : Fin N → ℝ} {ℓ : ℕ} {g : ℝ} (hg : 0 ≤ g)
    (hgap : ∀ k m : Fin N, k ≠ m → g ≤ |lam k - lam m|) :
    cfgRate N lam ℓ g = cfgRate N lam ℓ 0 := by
  funext i j
  unfold cfgRate
  split_ifs with h
  · rw [truncRate_eq (hgap i j h.1) hg, truncRate_eq (abs_nonneg _) le_rfl]
  · rfl

theorem cfgRate_zero_apply (lam : Fin N → ℝ) (ℓ : ℕ) {i j : Fin N} (hij : i ≠ j)
    (hd : labelDist i j < ℓ) : cfgRate N lam ℓ 0 i j = pairRate N lam i j := by
  unfold cfgRate pairRate
  rw [ite_eq_left ⟨hij, hd⟩, truncRate_eq (abs_nonneg _) le_rfl]

/-- The one-particle short jump sum in the form of `label_drift_le`. -/
theorem sum_cfgRate_eq (lam : Fin N → ℝ) (ℓ : ℕ) (f : ℝ → ℝ) (i : Fin N) :
    ∑ j ∈ univ.erase i, cfgRate N lam ℓ 0 i j * (f (lam j) - f (lam i)) =
      ∑ l, if l ≠ i ∧ labelDist i l < ℓ then
        pairRate N lam i l * (f (lam l) - f (lam i)) else 0 := by
  classical
  rw [← Finset.sum_erase (s := univ) (a := i) (by simp)]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hli : l ≠ i := (mem_erase.1 hl).1
  by_cases hd : labelDist i l < ℓ
  · rw [ite_eq_left ⟨hli, hd⟩, cfgRate_zero_apply lam ℓ (Ne.symm hli) hd]
  · rw [ite_eq_right (fun h => hd h.2)]
    simp [cfgRate, hd]

/-!
### The generator on the weight
-/

theorem momentGenerator_cfgWeight (c : Fin N → Fin N → ℝ) (φ : ℝ → ℝ) (lam : Fin N → ℝ)
    (ξ : Occ N) :
    momentGenerator c (cfgWeight φ lam) ξ =
      ∑ i, ∑ j ∈ univ.erase i, c i j * jumpCoeff ξ i j *
        (cfgWeight φ lam (remove ξ i) * (φ (lam j) - φ (lam i))) := by
  unfold momentGenerator
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := Ne.symm (mem_erase.1 hj).1
  rcases Nat.eq_zero_or_pos (ξ i) with hi | hi
  · simp [jumpCoeff_eq_zero_of_eq_zero ξ j hi]
  · rw [cfgWeight_move φ lam ξ hij, cfgWeight_eq_mul_remove φ lam ξ hi]; ring

/-- `∂_{λ_i} W(ξ) = ξ_i φ'(λ_i) W(ξ - δ_i)`. -/
def cfgD1 (φ φ1 : ℝ → ℝ) (lam : Fin N → ℝ) (ξ : Occ N) (i : Fin N) : ℝ :=
  (ξ i : ℝ) * φ1 (lam i) * cfgWeight φ lam (remove ξ i)

/-- `∂²_{λ_i} W(ξ) = ξ_i φ''(λ_i) W(ξ - δ_i) + ξ_i (ξ_i - 1) φ'(λ_i)² W(ξ - 2δ_i)`. -/
def cfgD2 (φ φ1 φ2 : ℝ → ℝ) (lam : Fin N → ℝ) (ξ : Occ N) (i : Fin N) : ℝ :=
  (ξ i : ℝ) * φ2 (lam i) * cfgWeight φ lam (remove ξ i) +
    (ξ i : ℝ) * ((ξ i : ℝ) - 1) * φ1 (lam i) ^ 2 * cfgWeight φ lam (remove (remove ξ i) i)

/-!
### Second-order pair bound
-/

/-- Mean value form: `φ(y) - φ(x) = φ'(z)(y - x)` with `z` between `x` and `y`. -/
theorem exists_mvt_between {φ φ1 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (x y : ℝ) :
    ∃ z, |z - x| ≤ |y - x| ∧ |z - y| ≤ |y - x| ∧ φ y - φ x = φ1 z * (y - x) := by
  have hc : Continuous φ := continuous_iff_continuousAt.2 fun z => (hφ z).continuousAt
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · obtain ⟨z, hz, hzeq⟩ := exists_hasDerivAt_eq_slope φ φ1 hxy hc.continuousOn
      (fun z _ => hφ z)
    refine ⟨z, ?_, ?_, ?_⟩
    · rw [abs_of_pos (by linarith [hz.1]), abs_of_pos (by linarith)]; linarith [hz.2]
    · rw [abs_of_neg (by linarith [hz.2]), abs_of_pos (by linarith)]; linarith [hz.1]
    · rw [hzeq]; field_simp [ne_of_gt (sub_pos.2 hxy)]
  · subst hxy; exact ⟨x, by simp, by simp, by simp⟩
  · obtain ⟨z, hz, hzeq⟩ := exists_hasDerivAt_eq_slope φ φ1 hxy hc.continuousOn
      (fun z _ => hφ z)
    refine ⟨z, ?_, ?_, ?_⟩
    · rw [abs_of_neg (by linarith [hz.2]), abs_of_neg (by linarith)]; linarith [hz.1]
    · rw [abs_of_pos (by linarith [hz.1]), abs_of_neg (by linarith)]; linarith [hz.2]
    · have hne : x - y ≠ 0 := ne_of_gt (sub_pos.2 hxy)
      have : φ1 z * (x - y) = φ x - φ y := by rw [hzeq]; field_simp
      linarith

/-- **Second-order pair bound**: `c_ij (φ_j - φ_i)² ≤ A² K² φ_i φ_j / N` for every pair. -/
theorem pair_sq_le (lam : Fin N → ℝ) (ℓ : ℕ) {φ φ1 : ℝ → ℝ}
    (hφ : ∀ z, HasDerivAt φ (φ1 z) z) {A K G : ℝ} (hφ0 : ∀ z, 0 ≤ φ z)
    (hA : ∀ z, |φ1 z| ≤ A * φ z) (hK0 : 0 ≤ K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) {i j : Fin N}
    (hshort : labelDist i j < ℓ → i ≠ j →
      |lam j - lam i| ≤ G ∨ (φ1 (lam i) = 0 ∧ φ (lam j) = φ (lam i))) :
    cfgRate N lam ℓ 0 i j * (φ (lam j) - φ (lam i)) ^ 2 ≤
      A ^ 2 * K ^ 2 * (φ (lam i) * φ (lam j)) / N := by
  have hR : 0 ≤ A ^ 2 * K ^ 2 * (φ (lam i) * φ (lam j)) / N := by
    have := hφ0 (lam i); have := hφ0 (lam j); positivity
  by_cases hs : i ≠ j ∧ labelDist i j < ℓ
  · rw [cfgRate_zero_apply lam ℓ hs.1 hs.2]
    rcases hshort hs.2 hs.1 with hc | hf
    · obtain ⟨z, hz1, hz2, hz⟩ := exists_mvt_between hφ (lam i) (lam j)
      rw [hz]
      by_cases hij : lam i = lam j
      · have h0 : lam j - lam i = 0 := by rw [hij]; ring
        rw [h0]; simpa using hR
      have hd : (lam i - lam j) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hij)
      have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have hzi : φ z ≤ K * φ (lam i) := hcomp (lam i) z (hz1.trans hc)
      have hzj : φ z ≤ K * φ (lam j) := hcomp (lam j) z (hz2.trans hc)
      have hφz := hφ0 z
      have h1 : φ1 z ^ 2 ≤ A ^ 2 * K ^ 2 * (φ (lam i) * φ (lam j)) := by
        have hA' : |φ1 z| ^ 2 ≤ (A * φ z) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hA z) 2
        rw [sq_abs] at hA'
        have hzz : φ z * φ z ≤ (K * φ (lam i)) * (K * φ (lam j)) :=
          mul_le_mul hzi hzj hφz (by have := hφ0 (lam i); positivity)
        calc φ1 z ^ 2 ≤ (A * φ z) ^ 2 := hA'
          _ = A ^ 2 * (φ z * φ z) := by ring
          _ ≤ A ^ 2 * ((K * φ (lam i)) * (K * φ (lam j))) :=
              mul_le_mul_of_nonneg_left hzz (sq_nonneg A)
          _ = _ := by ring
      have heq : pairRate N lam i j * (φ1 z * (lam j - lam i)) ^ 2 = φ1 z ^ 2 / N := by
        unfold pairRate
        rcases eq_or_ne (N : ℝ) 0 with hN | hN
        · rw [hN]; simp
        · have : (lam j - lam i) ^ 2 = (lam i - lam j) ^ 2 := by ring
          rw [mul_pow, this]; field_simp
      rw [heq]
      exact div_le_div_of_nonneg_right h1 hNr
    · have h0 : φ (lam j) - φ (lam i) = 0 := by rw [hf.2, sub_self]
      rw [h0]; simpa using hR
  · have : cfgRate N lam ℓ 0 i j = 0 := by unfold cfgRate; rw [ite_eq_right hs]
    rw [this, zero_mul]; exact hR

/-!
### The pointwise drift inequality
-/

theorem sum_cast_sector {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) : ∑ i, (ξ i : ℝ) = r := by
  rw [← Nat.cast_sum, mem_sector.1 hξ]

/-- `Σ_{i,j} ξ_i ξ_j = r²`. -/
theorem sum_sum_cast_mul_sector {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) :
    ∑ i, ∑ j, (ξ i : ℝ) * (ξ j : ℝ) = (r : ℝ) ^ 2 := by
  rw [sq, ← sum_cast_sector hξ, Finset.sum_mul_sum]

/-- **Drift cancellation on configurations, pointwise in `ξ`** (for the
`r`-particle short flow). -/
theorem cfg_point_drift_le (lam : Fin N → ℝ) (ℓ : ℕ)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B K G c₁ : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hK0 : 0 ≤ K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) (hc₁ : 0 < c₁)
    (hshort : ∀ k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k) = 0 ∧ φ (lam l) = φ (lam k)))
    (hlong : ∀ k l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|)
    {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) :
    momentGenerator (cfgRate N lam ℓ 0) (cfgWeight φ lam) ξ +
        ∑ i, (dysonDrift N lam i * cfgD1 φ φ1 lam ξ i + cfgD2 φ φ1 φ2 lam ξ i / (2 * N)) ≤
      (r * (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) * cfgWeight φ lam ξ := by
  classical
  set κ₁ := 2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N) with hκ₁
  set W := cfgWeight φ lam with hW
  set c := cfgRate N lam ℓ 0 with hc
  have hW0 : ∀ ζ, 0 ≤ W ζ := cfgWeight_nonneg hφ0 lam
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- the one-particle brackets
  set br : Fin N → ℝ := fun i => (∑ j ∈ univ.erase i, c i j * (φ (lam j) - φ (lam i))) +
    (φ1 (lam i) * dysonDrift N lam i + φ2 (lam i) / (2 * N)) with hbr
  have hbr_le : ∀ i, br i ≤ κ₁ * φ (lam i) := by
    intro i
    simp only [hbr, hc]
    rw [sum_cfgRate_eq lam ℓ φ i]
    exact label_drift_le lam ℓ hφ hφ1 hφ0 hA hA0 hB hB0 hK0 hcomp hc₁ i (hshort i)
      (hlong i)
  -- the three parts
  set P1 := ∑ i, (ξ i : ℝ) * W (remove ξ i) * br i with hP1
  set f : Fin N → Fin N → ℝ := fun i j => if i = j then 0 else
    c i j * ((ξ i : ℝ) * (ξ j : ℝ)) * (W (remove ξ i) * (φ (lam j) - φ (lam i))) with hf
  set P2 := ∑ i, ∑ j, f i j with hP2
  set P3 := ∑ i, (ξ i : ℝ) * ((ξ i : ℝ) - 1) * φ1 (lam i) ^ 2 *
    W (remove (remove ξ i) i) / (2 * N) with hP3
  have hsplit : momentGenerator c W ξ +
      ∑ i, (dysonDrift N lam i * cfgD1 φ φ1 lam ξ i + cfgD2 φ φ1 φ2 lam ξ i / (2 * N)) =
      P1 + P2 + P3 := by
    rw [hW, momentGenerator_cfgWeight]
    have hrow : ∀ i, ∑ j ∈ univ.erase i, c i j * jumpCoeff ξ i j *
        (W (remove ξ i) * (φ (lam j) - φ (lam i))) =
        (ξ i : ℝ) * W (remove ξ i) * ∑ j ∈ univ.erase i, c i j * (φ (lam j) - φ (lam i)) +
          ∑ j, f i j := by
      intro i
      rw [← Finset.sum_erase (s := univ) (a := i) (f := f i) (by simp [hf]), Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hji : j ≠ i := (mem_erase.1 hj).1
      simp only [hf, ite_eq_right (Ne.symm hji), jumpCoeff]
      ring
    rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_add_distrib]
    simp only [hP1, hP2, hP3, hbr, cfgD1, cfgD2, hW]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- part 1
  have h1 : P1 ≤ r * κ₁ * W ξ := by
    calc P1 ≤ ∑ i, (ξ i : ℝ) * W (remove ξ i) * (κ₁ * φ (lam i)) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbr_le i)
            (mul_nonneg (Nat.cast_nonneg _) (hW0 _))
      _ = ∑ i, κ₁ * ((ξ i : ℝ) * W ξ) := Finset.sum_congr rfl fun i _ => by
          rw [← cast_mul_cfgWeight_remove φ lam ξ i]; ring
      _ = r * κ₁ * W ξ := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, sum_cast_sector hξ]; ring
  -- part 2
  have hpair : ∀ i j, f i j + f j i ≤
      (ξ i : ℝ) * (ξ j : ℝ) * (A ^ 2 * K ^ 2 * W ξ / N) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [hf, ite_true, add_zero]
      have := hW0 ξ; positivity
    rcases Nat.eq_zero_or_pos (ξ i) with hi | hi
    · simp [hf, hij, Ne.symm hij, hi]
    rcases Nat.eq_zero_or_pos (ξ j) with hj | hj
    · simp [hf, hij, Ne.symm hij, hj]
    have hri : W (remove ξ i) = φ (lam j) * W (remove (remove ξ i) j) :=
      cfgWeight_eq_mul_remove φ lam _ (by rw [remove_apply_of_ne ξ (Ne.symm hij)]; exact hj)
    have hrj : W (remove ξ j) = φ (lam i) * W (remove (remove ξ i) j) := by
      rw [remove_comm ξ hij]
      exact cfgWeight_eq_mul_remove φ lam _ (by rw [remove_apply_of_ne ξ hij]; exact hi)
    have hWξ : W ξ = φ (lam i) * φ (lam j) * W (remove (remove ξ i) j) := by
      calc W ξ = φ (lam i) * W (remove ξ i) := cfgWeight_eq_mul_remove φ lam ξ hi
        _ = _ := by rw [hri]; ring
    have hsum : f i j + f j i = (ξ i : ℝ) * (ξ j : ℝ) * W (remove (remove ξ i) j) *
        (c i j * (φ (lam j) - φ (lam i)) ^ 2) := by
      simp only [hf, ite_eq_right hij, ite_eq_right (Ne.symm hij), hri, hrj, hc, cfgRate_symm lam ℓ 0 j i]
      ring
    have hp := pair_sq_le lam ℓ hφ hφ0 hA hK0 hcomp (i := i) (j := j)
      (fun hd hne => hshort i j (Ne.symm hne) hd)
    rw [hsum, hWξ]
    have hnn : 0 ≤ (ξ i : ℝ) * (ξ j : ℝ) * W (remove (remove ξ i) j) :=
      mul_nonneg (by positivity) (hW0 _)
    calc _ ≤ (ξ i : ℝ) * (ξ j : ℝ) * W (remove (remove ξ i) j) *
          (A ^ 2 * K ^ 2 * (φ (lam i) * φ (lam j)) / N) := mul_le_mul_of_nonneg_left hp hnn
      _ = _ := by ring
  have h2 : P2 ≤ r ^ 2 * (A ^ 2 * K ^ 2) / (2 * N) * W ξ := by
    have hsym : 2 * P2 = ∑ i, ∑ j, (f i j + f j i) := by
      simp only [hP2, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => f j i)]; ring
    have hle : ∑ i, ∑ j, (f i j + f j i) ≤
        ∑ i, ∑ j, (ξ i : ℝ) * (ξ j : ℝ) * (A ^ 2 * K ^ 2 * W ξ / N) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    have hRHS : ∑ i, ∑ j, (ξ i : ℝ) * (ξ j : ℝ) * (A ^ 2 * K ^ 2 * W ξ / N) =
        (r : ℝ) ^ 2 * (A ^ 2 * K ^ 2 * W ξ / N) := by
      rw [← sum_sum_cast_mul_sector hξ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    rw [hRHS] at hle
    have : P2 ≤ (r : ℝ) ^ 2 * (A ^ 2 * K ^ 2 * W ξ / N) / 2 := by linarith
    calc P2 ≤ (r : ℝ) ^ 2 * (A ^ 2 * K ^ 2 * W ξ / N) / 2 := this
      _ = _ := by
        rcases eq_or_ne (N : ℝ) 0 with hN | hN
        · rw [hN]; simp
        · field_simp
  -- part 3
  have h3 : P3 ≤ r ^ 2 * A ^ 2 / (2 * N) * W ξ := by
    have hpt : ∀ i, (ξ i : ℝ) * ((ξ i : ℝ) - 1) * φ1 (lam i) ^ 2 *
        W (remove (remove ξ i) i) / (2 * N) ≤ (ξ i : ℝ) ^ 2 * (A ^ 2 * W ξ / (2 * N)) := by
      intro i
      have hrhs : 0 ≤ (ξ i : ℝ) ^ 2 * (A ^ 2 * W ξ / (2 * N)) := by
        have := hW0 ξ; positivity
      rcases Nat.lt_or_ge (ξ i) 2 with hlt | hge
      · have hz : (ξ i : ℝ) * ((ξ i : ℝ) - 1) = 0 := by
          interval_cases h : ξ i <;> simp
        rw [hz]; simpa using hrhs
      · have hi1 : 0 < ξ i := by omega
        have hi2 : 0 < remove ξ i i := by rw [remove_apply_self]; omega
        have hWξ : W ξ = φ (lam i) ^ 2 * W (remove (remove ξ i) i) := by
          have hr2 : W (remove ξ i) = φ (lam i) * W (remove (remove ξ i) i) :=
            cfgWeight_eq_mul_remove φ lam _ hi2
          calc W ξ = φ (lam i) * W (remove ξ i) := cfgWeight_eq_mul_remove φ lam ξ hi1
            _ = _ := by rw [hr2]; ring
        have hA2 : φ1 (lam i) ^ 2 ≤ A ^ 2 * φ (lam i) ^ 2 := by
          have := pow_le_pow_left₀ (abs_nonneg _) (hA (lam i)) 2
          rw [sq_abs] at this; nlinarith
        have hξ1 : (0 : ℝ) ≤ (ξ i : ℝ) * ((ξ i : ℝ) - 1) := by
          have : (2 : ℝ) ≤ ξ i := by exact_mod_cast hge
          nlinarith
        have hWrr := hW0 (remove (remove ξ i) i)
        rw [hWξ]
        have hle : (ξ i : ℝ) * ((ξ i : ℝ) - 1) ≤ (ξ i : ℝ) ^ 2 := by nlinarith
        have key : (ξ i : ℝ) * ((ξ i : ℝ) - 1) * φ1 (lam i) ^ 2 * W (remove (remove ξ i) i) ≤
            (ξ i : ℝ) ^ 2 * (A ^ 2 * (φ (lam i) ^ 2 * W (remove (remove ξ i) i))) := by
          calc _ ≤ (ξ i : ℝ) * ((ξ i : ℝ) - 1) * (A ^ 2 * φ (lam i) ^ 2) *
                W (remove (remove ξ i) i) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA2 hξ1) hWrr
            _ ≤ (ξ i : ℝ) ^ 2 * (A ^ 2 * φ (lam i) ^ 2) * W (remove (remove ξ i) i) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hle (by positivity)) hWrr
            _ = _ := by ring
        calc _ ≤ (ξ i : ℝ) ^ 2 * (A ^ 2 * (φ (lam i) ^ 2 * W (remove (remove ξ i) i))) /
              (2 * N) := div_le_div_of_nonneg_right key (by positivity)
          _ = _ := by ring
    calc P3 ≤ ∑ i, (ξ i : ℝ) ^ 2 * (A ^ 2 * W ξ / (2 * N)) := Finset.sum_le_sum fun i _ => hpt i
      _ = (∑ i, (ξ i : ℝ) ^ 2) * (A ^ 2 * W ξ / (2 * N)) := by rw [Finset.sum_mul]
      _ ≤ (∑ i, (ξ i : ℝ)) ^ 2 * (A ^ 2 * W ξ / (2 * N)) := by
          refine mul_le_mul_of_nonneg_right
            (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Nat.cast_nonneg _) ?_
          have := hW0 ξ; positivity
      _ = _ := by rw [sum_cast_sector hξ]; ring
  rw [hsplit]
  calc P1 + P2 + P3 ≤ r * κ₁ * W ξ + r ^ 2 * (A ^ 2 * K ^ 2) / (2 * N) * W ξ +
      r ^ 2 * A ^ 2 / (2 * N) * W ξ := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

/-- **Drift cancellation on configurations, summed form.** For `v ≥ 0` on the sector,
`Σ_ξ W(ξ)(𝓢 v)(ξ) + Σ_ξ v(ξ) Σ_i (D_i ∂_iW(ξ) + ∂²_iW(ξ)/(2N)) ≤ κ_r Σ_ξ W(ξ) v(ξ)`. -/
theorem cfg_drift_le (lam : Fin N → ℝ) (ℓ : ℕ)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B K G c₁ : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hK0 : 0 ≤ K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) (hc₁ : 0 < c₁)
    (hshort : ∀ k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k) = 0 ∧ φ (lam l) = φ (lam k)))
    (hlong : ∀ k l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|)
    (r : ℕ) (v : Occ N → ℝ) (hv : ∀ ξ ∈ sector N r, 0 ≤ v ξ) :
    ∑ ξ ∈ sector N r, cfgWeight φ lam ξ * momentGenerator (cfgRate N lam ℓ 0) v ξ +
        ∑ ξ ∈ sector N r, v ξ *
          ∑ i, (dysonDrift N lam i * cfgD1 φ φ1 lam ξ i + cfgD2 φ φ1 φ2 lam ξ i / (2 * N)) ≤
      (r * (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) *
        ∑ ξ ∈ sector N r, cfgWeight φ lam ξ * v ξ := by
  rw [sum_mul_momentGenerator_symm (cfgRate_symm lam ℓ 0) r v (cfgWeight φ lam),
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun ξ hξ => ?_
  rw [← mul_add]
  calc v ξ * (momentGenerator (cfgRate N lam ℓ 0) (cfgWeight φ lam) ξ +
        ∑ i, (dysonDrift N lam i * cfgD1 φ φ1 lam ξ i + cfgD2 φ φ1 φ2 lam ξ i / (2 * N)))
      ≤ v ξ * ((r * (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) * cfgWeight φ lam ξ) :=
        mul_le_mul_of_nonneg_left
          (cfg_point_drift_le lam ℓ hφ hφ1 hφ0 hA hA0 hB hB0 hK0 hcomp hc₁ hshort hlong hξ)
          (hv ξ hξ)
    _ = _ := by ring

end BlockBand.Palm.MomentFlow
