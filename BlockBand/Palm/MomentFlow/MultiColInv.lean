module

public import BlockBand.Palm.MomentFlow.MultiColAbsPoint

/-!
# Column form: the drift of the reciprocal matching weight

`𝓢w + Σ_i (D_i ∂_i w + ∂²_i w/(2N)) = -(𝓢W + Σ_i(D_i F1 + F2/(2N)))/W² + Γ_jump/W² + Σ_i F1²/(N W³)`

with `Γ_jump = Σ c_ij ζ_i(1+ζ_j)(W(ζ^{ij}) - W(ζ))²/W(ζ^{ij})`. The first term is bounded by
`perm_point_drift_abs`; `Γ_jump ≤ r(2ℓ + r)A²K³ W/N` (one short jump changes `W` by a factor
in `[1/K, 1 + AK|Δλ|]`); `Σ_i F1² ≤ r²A² W²`. Hence (`inv_point_drift_le`)

`𝓢w + Σ_i (D_i ∂_i w + ∂²_i w/(2N)) ≤ (κ_r + r(2ℓ+r)A²K³/N + r²A²/N) w`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization

variable {N r : ℕ}

/-- `∂_{λ_i} W(ζ)`. -/
def permF1 (φ φ1 : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (ζ : Occ N) (i : Fin N) : ℝ :=
  cfgFact ζ * ∑ y ∈ labs r ζ, permD1 φ φ1 lam c y i

/-- `∂²_{λ_i} W(ζ)`. -/
def permF2 (φ φ1 φ2 : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (ζ : Occ N) (i : Fin N) : ℝ :=
  cfgFact ζ * ∑ y ∈ labs r ζ, permD2 φ φ1 φ2 lam c y i

theorem permW_pos {φ : ℝ → ℝ} (hφ : ∀ z, 0 < φ z) (lam : Fin N → ℝ) (c : Fin r → ℝ)
    {ζ : Occ N} (hζ : ζ ∈ sector N r) : 0 < permW φ lam c ζ := by
  obtain ⟨y, hy⟩ := exists_occOf r ζ hζ
  have hy' : y ∈ labs r ζ := mem_labs.2 hy
  unfold permW
  refine mul_pos (cfgFact_pos ζ) ?_
  exact Finset.sum_pos (fun y _ => Finset.prod_pos fun m _ => hφ _) ⟨y, hy'⟩

/-- `Σ_i F1_i² ≤ r² A² W²`. -/
theorem sum_sq_permF1_le {φ φ1 : ℝ → ℝ} {A : ℝ} (hφ0 : ∀ z, 0 ≤ φ z)
    (hA : ∀ z, |φ1 z| ≤ A * φ z) (_hA0 : 0 ≤ A) (lam : Fin N → ℝ) (c : Fin r → ℝ) (ζ : Occ N) :
    ∑ i, permF1 φ φ1 lam c ζ i ^ 2 ≤ (r : ℝ) ^ 2 * A ^ 2 * permW φ lam c ζ ^ 2 := by
  classical
  have hpt : ∀ y i, |permD1 φ φ1 lam c y i| ≤
      A * ((univ.filter fun m => y m = i).card : ℝ) * pW φ lam c y := by
    intro y i
    unfold permD1
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m, |if y m = i then φ1 (lam i - c m) * pWx φ lam c y m else 0|
        ≤ ∑ m, if y m = i then A * pW φ lam c y else 0 := Finset.sum_le_sum fun m _ => by
          by_cases hm : y m = i
          · rw [ite_eq_left hm, ite_eq_left hm, abs_mul, abs_of_nonneg (pWx_nonneg hφ0 _ _ _ _),
              pW_eq_mul φ lam c y m, hm]
            calc |φ1 (lam i - c m)| * pWx φ lam c y m ≤ A * φ (lam i - c m) * pWx φ lam c y m :=
                  mul_le_mul_of_nonneg_right (hA _) (pWx_nonneg hφ0 _ _ _ _)
              _ = _ := by ring
          · rw [ite_eq_right hm, ite_eq_right hm, abs_zero]
      _ = _ := by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
  have hF : ∀ i, |permF1 φ φ1 lam c ζ i| ≤ A * cfgFact ζ *
      ∑ y ∈ labs r ζ, ((univ.filter fun m => y m = i).card : ℝ) * pW φ lam c y := by
    intro i
    unfold permF1
    rw [abs_mul, abs_of_pos (cfgFact_pos ζ)]
    calc cfgFact ζ * |∑ y ∈ labs r ζ, permD1 φ φ1 lam c y i|
        ≤ cfgFact ζ * ∑ y ∈ labs r ζ, A * ((univ.filter fun m => y m = i).card : ℝ) *
          pW φ lam c y :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun y _ => hpt y i)) (cfgFact_pos ζ).le
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
  have hsum : ∑ i, |permF1 φ φ1 lam c ζ i| ≤ r * A * permW φ lam c ζ := by
    calc ∑ i, |permF1 φ φ1 lam c ζ i| ≤ ∑ i, A * cfgFact ζ *
          ∑ y ∈ labs r ζ, ((univ.filter fun m => y m = i).card : ℝ) * pW φ lam c y :=
          Finset.sum_le_sum fun i _ => hF i
      _ = A * cfgFact ζ * ∑ y ∈ labs r ζ, (r : ℝ) * pW φ lam c y := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_mul]
          congr 1
          have := mem_sector.1 (occOf_mem_sector (N := N) y)
          exact_mod_cast this
      _ = _ := by unfold permW; rw [← Finset.mul_sum]; ring
  have h0 : ∀ i ∈ (univ : Finset (Fin N)), 0 ≤ |permF1 φ φ1 lam c ζ i| := fun i _ => abs_nonneg _
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg h0
  simp only [sq_abs] at hsq
  have hW0 : 0 ≤ permW φ lam c ζ :=
    mul_nonneg (cfgFact_pos _).le (Finset.sum_nonneg fun y _ => pW_nonneg hφ0 _ _ y)
  calc ∑ i, permF1 φ φ1 lam c ζ i ^ 2 ≤ (∑ i, |permF1 φ φ1 lam c ζ i|) ^ 2 := hsq
    _ ≤ (r * A * permW φ lam c ζ) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => abs_nonneg _) hsum 2
    _ = _ := by ring

/-- One short jump changes the weight by a controlled factor. -/
theorem permW_jump_bounds (lam : Fin N → ℝ) (_ℓ : ℕ) (c : Fin r → ℝ) {φ φ1 : ℝ → ℝ}
    (hφ : ∀ z, HasDerivAt φ (φ1 z) z) {A K G : ℝ} (hφp : ∀ z, 0 < φ z)
    (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A) (hK0 : 0 < K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) {ζ : Occ N} {i j : Fin N} (hij : i ≠ j)
    (hi : 0 < ζ i) :
    (|lam j - lam i| ≤ G → |permW φ lam c (move ζ i j) - permW φ lam c ζ| ≤
        A * K * |lam j - lam i| * permW φ lam c ζ ∧
      permW φ lam c ζ / K ≤ permW φ lam c (move ζ i j)) ∧
    ((∀ m, φ (lam j - c m) = φ (lam i - c m)) →
      permW φ lam c (move ζ i j) = permW φ lam c ζ) := by
  classical
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => (hφp z).le
  have hJ := jump_permW (r := r) φ lam c hij hi
  have hζi : (0 : ℝ) < ζ i := by exact_mod_cast hi
  set S := ∑ y ∈ labs r ζ, ∑ p ∈ univ.filter (fun p => y p = i), pW φ lam c y with hS
  have hSf : cfgFact ζ * S = (ζ i : ℝ) * permW φ lam c ζ := by
    rw [hS, permW, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_filter_eq_occOf, mem_labs.1 hy]; ring
  have hdiff : ∀ y, ∀ p ∈ univ.filter (fun p => y p = i),
      pW φ lam c (Function.update y p j) - pW φ lam c y =
        (φ (lam j - c p) - φ (lam i - c p)) * pWx φ lam c y p := by
    intro y p hp
    have hp' : y p = i := (Finset.mem_filter.1 hp).2
    rw [pW_update, pW_eq_mul φ lam c y p, hp']; ring
  refine ⟨fun hc => ⟨?_, ?_⟩, fun hflat => ?_⟩
  · have hpt : ∀ y, ∀ p ∈ univ.filter (fun p => y p = i),
        |pW φ lam c (Function.update y p j) - pW φ lam c y| ≤
          A * K * |lam j - lam i| * pW φ lam c y := by
      intro y p hp
      have hp' : y p = i := (Finset.mem_filter.1 hp).2
      rw [hdiff y p hp]
      obtain ⟨z, hz1, -, hz⟩ := exists_mvt_between (fun t => HasDerivAt.comp_sub_const t (c p)
        (hφ (t - c p))) (lam i) (lam j)
      rw [hz, abs_mul, abs_mul, abs_of_nonneg (pWx_nonneg hφ0 _ _ _ _)]
      have h1 : |φ1 (z - c p)| ≤ A * K * φ (lam i - c p) := by
        have := hcomp (lam i - c p) (z - c p) (by rw [sub_sub_sub_cancel_right]; exact hz1.trans hc)
        calc |φ1 (z - c p)| ≤ A * φ (z - c p) := hA _
          _ ≤ A * (K * φ (lam i - c p)) := mul_le_mul_of_nonneg_left this hA0
          _ = _ := by ring
      rw [pW_eq_mul φ lam c y p, hp']
      calc |φ1 (z - c p)| * |lam j - lam i| * pWx φ lam c y p
          ≤ A * K * φ (lam i - c p) * |lam j - lam i| * pWx φ lam c y p :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
              (pWx_nonneg hφ0 _ _ _ _)
        _ = _ := by ring
    have h1 : (ζ i : ℝ) * |permW φ lam c (move ζ i j) - permW φ lam c ζ| ≤
        (ζ i : ℝ) * (A * K * |lam j - lam i| * permW φ lam c ζ) := by
      rw [← abs_of_pos hζi, ← abs_mul, hJ, abs_mul, abs_of_pos (cfgFact_pos ζ), abs_of_pos hζi]
      calc cfgFact ζ * |∑ y ∈ labs r ζ, ∑ p ∈ univ.filter (fun p => y p = i),
            (pW φ lam c (Function.update y p j) - pW φ lam c y)|
          ≤ cfgFact ζ * ∑ y ∈ labs r ζ, ∑ p ∈ univ.filter (fun p => y p = i),
            A * K * |lam j - lam i| * pW φ lam c y :=
            mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun y _ => (Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun p hp => hpt y p hp))) (cfgFact_pos ζ).le
        _ = A * K * |lam j - lam i| * (cfgFact ζ * S) := by
            rw [hS]; simp only [← Finset.mul_sum]; ring
        _ = _ := by rw [hSf]; ring
    exact le_of_mul_le_mul_left h1 hζi
  · have hpt : ∀ y, ∀ p ∈ univ.filter (fun p => y p = i),
        pW φ lam c y / K ≤ pW φ lam c (Function.update y p j) := by
      intro y p hp
      have hp' : y p = i := (Finset.mem_filter.1 hp).2
      rw [pW_update, pW_eq_mul φ lam c y p, hp', div_le_iff₀ hK0]
      have := hcomp (lam j - c p) (lam i - c p) (by
        rw [sub_sub_sub_cancel_right, abs_sub_comm]; exact hc)
      have hx := pWx_nonneg hφ0 lam c y p
      nlinarith
    have hmove : (ζ i : ℝ) * permW φ lam c (move ζ i j) = cfgFact ζ *
        ∑ y ∈ labs r ζ, ∑ p ∈ univ.filter (fun p => y p = i),
          pW φ lam c (Function.update y p j) := by
      have : (ζ i : ℝ) * permW φ lam c (move ζ i j) =
          (ζ i : ℝ) * (permW φ lam c (move ζ i j) - permW φ lam c ζ) +
            (ζ i : ℝ) * permW φ lam c ζ := by ring
      rw [this, hJ, ← hSf, hS, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun y _ => by rw [← Finset.sum_add_distrib]; simp
    have h2 : (ζ i : ℝ) * (permW φ lam c ζ / K) ≤ (ζ i : ℝ) * permW φ lam c (move ζ i j) := by
      rw [hmove, mul_div_assoc', ← hSf, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (cfgFact_pos ζ).le
      rw [hS, Finset.sum_div]
      exact Finset.sum_le_sum fun y _ => by
        rw [Finset.sum_div]; exact Finset.sum_le_sum fun p hp => hpt y p hp
    exact le_of_mul_le_mul_left h2 hζi
  · have h0 : (ζ i : ℝ) * (permW φ lam c (move ζ i j) - permW φ lam c ζ) = 0 := by
      rw [hJ]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ =>
        Finset.sum_eq_zero fun p hp => ?_)
      rw [hdiff y p hp, hflat p, sub_self, zero_mul]
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (ne_of_gt hζi)
    · linarith

/-- **Drift of the reciprocal matching weight, pointwise.** -/
theorem inv_point_drift_le (lam : Fin N → ℝ) (ℓ : ℕ) (c : Fin r → ℝ)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B K G c₁ : ℝ} (hφp : ∀ z, 0 < φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hK0 : 0 < K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) (hc₁ : 0 < c₁)
    (hshort : ∀ m k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k - c m) = 0 ∧ φ (lam l - c m) = φ (lam k - c m)))
    (hlong : ∀ k l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|)
    {ζ : Occ N} (hζ : ζ ∈ sector N r) :
    momentGenerator (cfgRate N lam ℓ 0) (fun η => (permW φ lam c η)⁻¹) ζ +
        ∑ i, (dysonDrift N lam i * (-(permF1 φ φ1 lam c ζ i) / permW φ lam c ζ ^ 2) +
          (-(permF2 φ φ1 φ2 lam c ζ i) / permW φ lam c ζ ^ 2 +
            2 * permF1 φ φ1 lam c ζ i ^ 2 / permW φ lam c ζ ^ 3) / (2 * N)) ≤
      ((r * (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) +
        r * (2 * ℓ + r) * A ^ 2 * K ^ 3 / N + r ^ 2 * A ^ 2 / N) * (permW φ lam c ζ)⁻¹ := by
  classical
  set κr := (r * (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) with hκr
  set cr := cfgRate N lam ℓ 0 with hcrdef
  set W := permW φ lam c with hWdef
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => (hφp z).le
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hf : 0 < W ζ := permW_pos hφp lam c hζ
  set f := W ζ with hfdef
  -- the generator of the reciprocal
  set Γ : ℝ := ∑ i, ∑ j ∈ univ.erase i, cr i j * jumpCoeff ζ i j *
    ((W (move ζ i j) - f) ^ 2 / W (move ζ i j)) with hΓ
  have hgen : momentGenerator cr (fun η => (W η)⁻¹) ζ =
      -(momentGenerator cr W ζ) / f ^ 2 + Γ / f ^ 2 := by
    have key : ∀ i, ∀ j ∈ univ.erase i, cr i j * jumpCoeff ζ i j *
        ((fun η => (W η)⁻¹) (move ζ i j) - (fun η => (W η)⁻¹) ζ) =
        (-(cr i j * jumpCoeff ζ i j * (W (move ζ i j) - f)) +
          cr i j * jumpCoeff ζ i j * ((W (move ζ i j) - f) ^ 2 / W (move ζ i j))) / f ^ 2 := by
      intro i j hj
      have hij : i ≠ j := Ne.symm (mem_erase.1 hj).1
      rcases Nat.eq_zero_or_pos (ζ i) with hi | hi
      · simp [jumpCoeff_eq_zero_of_eq_zero ζ j hi]
      · have hf' : 0 < W (move ζ i j) := permW_pos hφp lam c (move_mem_sector hζ hij hi)
        dsimp only
        rw [← hfdef]
        field_simp [hf.ne', hf'.ne']
        ring
    unfold momentGenerator
    rw [hΓ]
    calc ∑ i, ∑ j ∈ univ.erase i, cr i j * jumpCoeff ζ i j *
          ((fun η => (W η)⁻¹) (move ζ i j) - (fun η => (W η)⁻¹) ζ)
        = ∑ i, ∑ j ∈ univ.erase i, (-(cr i j * jumpCoeff ζ i j * (W (move ζ i j) - f)) +
          cr i j * jumpCoeff ζ i j * ((W (move ζ i j) - f) ^ 2 / W (move ζ i j))) / f ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => key i j hj
      _ = (∑ i, ∑ j ∈ univ.erase i, (-(cr i j * jumpCoeff ζ i j * (W (move ζ i j) - f)) +
          cr i j * jumpCoeff ζ i j * ((W (move ζ i j) - f) ^ 2 / W (move ζ i j)))) / f ^ 2 := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => (Finset.sum_div _ _ _).symm
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
          ring
  -- Γ bound
  have hΓle : Γ ≤ r * (2 * ℓ + r) * A ^ 2 * K ^ 3 / N * f := by
    have hpt : ∀ i, ∀ j ∈ univ.erase i, cr i j * jumpCoeff ζ i j *
        ((W (move ζ i j) - f) ^ 2 / W (move ζ i j)) ≤
        (if labelDist i j < ℓ then (ζ i : ℝ) * (1 + ζ j) * (A ^ 2 * K ^ 3 / N * f) else 0) := by
      intro i j hj
      have hij : i ≠ j := Ne.symm (mem_erase.1 hj).1
      have hcr0 : 0 ≤ cr i j := cfgRate_nonneg lam ℓ 0 i j
      rcases Nat.eq_zero_or_pos (ζ i) with hi | hi
      · rw [jumpCoeff_eq_zero_of_eq_zero ζ j hi, mul_zero, zero_mul]
        split_ifs <;> simp [hi]
      have hf' : 0 < W (move ζ i j) := permW_pos hφp lam c (move_mem_sector hζ hij hi)
      by_cases hd : labelDist i j < ℓ
      · rw [ite_eq_left hd]
        have hJ0 : 0 ≤ jumpCoeff ζ i j := jumpCoeff_nonneg ζ i j
        obtain ⟨hclose, hflat⟩ := permW_jump_bounds lam ℓ c hφ hφp hA hA0 hK0 hcomp hij hi
        rw [← hWdef] at hclose hflat
        by_cases hc : |lam j - lam i| ≤ G
        · obtain ⟨h1, h2⟩ := hclose hc
          by_cases hΔ : lam i = lam j
          · have hzero : ∀ m, φ (lam j - c m) = φ (lam i - c m) := fun m => by rw [hΔ]
            rw [hflat hzero, sub_self]
            simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
              mul_zero]
            positivity
          have hcrv : cr i j * (lam j - lam i) ^ 2 = 1 / N := by
            rw [hcrdef, cfgRate_zero_apply lam ℓ hij hd]
            unfold pairRate
            have hd2 : (lam i - lam j) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hΔ)
            rcases eq_or_ne (N : ℝ) 0 with hN | hN
            · rw [hN]; simp
            · field_simp; ring
          have hsq : (W (move ζ i j) - f) ^ 2 ≤ (A * K * |lam j - lam i| * f) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          have hq : (W (move ζ i j) - f) ^ 2 / W (move ζ i j) ≤
              (A * K * |lam j - lam i| * f) ^ 2 / (f / K) :=
            div_le_div₀ (sq_nonneg _) hsq (by positivity) h2
          have hq' : (A * K * |lam j - lam i| * f) ^ 2 / (f / K) =
              A ^ 2 * K ^ 3 * f * (lam j - lam i) ^ 2 := by
            rw [mul_pow, mul_pow, mul_pow, sq_abs]; field_simp
          calc cr i j * jumpCoeff ζ i j * ((W (move ζ i j) - f) ^ 2 / W (move ζ i j))
              ≤ cr i j * jumpCoeff ζ i j * (A ^ 2 * K ^ 3 * f * (lam j - lam i) ^ 2) := by
                rw [← hq']; exact mul_le_mul_of_nonneg_left hq (mul_nonneg hcr0 hJ0)
            _ = jumpCoeff ζ i j * (A ^ 2 * K ^ 3 * f) * (cr i j * (lam j - lam i) ^ 2) := by ring
            _ = _ := by rw [hcrv]; unfold jumpCoeff; ring
        · have hzero : ∀ m, φ (lam j - c m) = φ (lam i - c m) := by
            intro m
            rcases hshort m i j (Ne.symm hij) hd with h | h
            · exact absurd h hc
            · exact h.2
          rw [hflat hzero, sub_self]
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, mul_zero]
          positivity
      · rw [ite_eq_right hd]
        have : cr i j = 0 := by rw [hcrdef]; unfold cfgRate; rw [ite_eq_right fun h => hd h.2]
        rw [this, zero_mul, zero_mul]
    calc Γ ≤ ∑ i, ∑ j ∈ univ.erase i,
          (if labelDist i j < ℓ then (ζ i : ℝ) * (1 + ζ j) * (A ^ 2 * K ^ 3 / N * f) else 0) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => hpt i j hj
      _ ≤ ∑ i, (ζ i : ℝ) * (2 * ℓ + r) * (A ^ 2 * K ^ 3 / N * f) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hX : 0 ≤ A ^ 2 * K ^ 3 / N * f := by positivity
          rw [← Finset.sum_filter]
          have hsub : ((univ.erase i).filter fun j => labelDist i j < ℓ) ⊆
              univ.filter fun l : Fin N => l ≠ i ∧ labelDist i l < ℓ := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
              true_and] at hj ⊢
            exact hj
          have hcard := card_short_le i ℓ
          calc ∑ j ∈ (univ.erase i).filter (fun j => labelDist i j < ℓ),
                (ζ i : ℝ) * (1 + ζ j) * (A ^ 2 * K ^ 3 / N * f)
              = (ζ i : ℝ) * (A ^ 2 * K ^ 3 / N * f) *
                  ∑ j ∈ (univ.erase i).filter (fun j => labelDist i j < ℓ), (1 + (ζ j : ℝ)) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ ≤ (ζ i : ℝ) * (A ^ 2 * K ^ 3 / N * f) * (2 * ℓ + r) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
                have h1 : (((univ.erase i).filter fun j => labelDist i j < ℓ).card : ℝ) ≤ 2 * ℓ :=
                  le_trans (by exact_mod_cast Finset.card_le_card hsub) hcard
                have h2 : ∑ j ∈ (univ.erase i).filter (fun j => labelDist i j < ℓ), (ζ j : ℝ) ≤
                    r := by
                  rw [← sum_cast_sector hζ]
                  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                    fun _ _ _ => Nat.cast_nonneg _
                linarith
            _ = _ := by ring
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, sum_cast_sector hζ]; ring
  -- the drift of `W`, two-sided
  have habs := perm_point_drift_abs lam ℓ c hφ hφ1 hφ0 hA hA0 hB hB0 hK0.le hcomp hc₁ hshort
    hlong ζ
  set L := momentGenerator cr W ζ +
    ∑ i, (dysonDrift N lam i * (cfgFact ζ * ∑ y ∈ labs r ζ, permD1 φ φ1 lam c y i) +
      cfgFact ζ * ∑ y ∈ labs r ζ, permD2 φ φ1 φ2 lam c y i / (2 * N)) with hL
  have hLe : L = momentGenerator cr W ζ +
      ∑ i, (dysonDrift N lam i * permF1 φ φ1 lam c ζ i + permF2 φ φ1 φ2 lam c ζ i / (2 * N)) := by
    rw [hL]; congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [permF1, permF2, Finset.mul_sum, Finset.sum_div, mul_div_assoc]
  have hF1 := sum_sq_permF1_le hφ0 hA hA0 lam c ζ
  -- assembly
  have hexp : momentGenerator cr (fun η => (W η)⁻¹) ζ +
      ∑ i, (dysonDrift N lam i * (-(permF1 φ φ1 lam c ζ i) / f ^ 2) +
        (-(permF2 φ φ1 φ2 lam c ζ i) / f ^ 2 + 2 * permF1 φ φ1 lam c ζ i ^ 2 / f ^ 3) / (2 * N)) =
      -L / f ^ 2 + Γ / f ^ 2 + (∑ i, permF1 φ φ1 lam c ζ i ^ 2) / (N * f ^ 3) := by
    rw [hgen, hLe]
    have hs : ∑ i, (dysonDrift N lam i * (-(permF1 φ φ1 lam c ζ i) / f ^ 2) +
        (-(permF2 φ φ1 φ2 lam c ζ i) / f ^ 2 + 2 * permF1 φ φ1 lam c ζ i ^ 2 / f ^ 3) / (2 * N)) =
        -(∑ i, (dysonDrift N lam i * permF1 φ φ1 lam c ζ i +
          permF2 φ φ1 φ2 lam c ζ i / (2 * N))) / f ^ 2 +
        (∑ i, permF1 φ φ1 lam c ζ i ^ 2) / (N * f ^ 3) := by
      rw [neg_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases eq_or_ne (N : ℝ) 0 with hN | hN
      · rw [hN]; simp only [mul_zero, div_zero, add_zero, zero_mul]; ring
      · field_simp [hf.ne', hN]
        ring
    rw [hs]
    ring
  rw [hexp]
  have hfi : 0 < f⁻¹ := inv_pos.2 hf
  have t1 : -L / f ^ 2 ≤ κr * f⁻¹ := by
    have : -L ≤ κr * f := by
      have := (abs_le.1 habs).1; rw [hκr]; linarith
    calc -L / f ^ 2 ≤ κr * f / f ^ 2 := div_le_div_of_nonneg_right this (by positivity)
      _ = κr * f⁻¹ := by field_simp
  have t2 : Γ / f ^ 2 ≤ r * (2 * ℓ + r) * A ^ 2 * K ^ 3 / N * f⁻¹ := by
    calc Γ / f ^ 2 ≤ r * (2 * ℓ + r) * A ^ 2 * K ^ 3 / N * f / f ^ 2 :=
          div_le_div_of_nonneg_right hΓle (by positivity)
      _ = _ := by field_simp
  have t3 : (∑ i, permF1 φ φ1 lam c ζ i ^ 2) / (N * f ^ 3) ≤ r ^ 2 * A ^ 2 / N * f⁻¹ := by
    rcases eq_or_ne (N : ℝ) 0 with hN | hN
    · rw [hN]; simp
    have hNp : (0 : ℝ) < N := lt_of_le_of_ne hNr (Ne.symm hN)
    calc (∑ i, permF1 φ φ1 lam c ζ i ^ 2) / (N * f ^ 3) ≤ (r : ℝ) ^ 2 * A ^ 2 * f ^ 2 / (N * f ^ 3) :=
          div_le_div_of_nonneg_right hF1 (by positivity)
      _ = _ := by field_simp
  calc -L / f ^ 2 + Γ / f ^ 2 + (∑ i, permF1 φ φ1 lam c ζ i ^ 2) / (N * f ^ 3)
      ≤ κr * f⁻¹ + r * (2 * ℓ + r) * A ^ 2 * K ^ 3 / N * f⁻¹ + r ^ 2 * A ^ 2 / N * f⁻¹ :=
        add_le_add (add_le_add t1 t2) t3
    _ = _ := by ring

end BlockBand.Palm.MomentFlow
