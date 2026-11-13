module

public import BlockBand.Palm.MomentFlow.EventTime

/-!
# Isotropic upper bound on the full height range: deterministic mesh ingredients

* `resolvent_quad_im_lipschitz`: `Im q*G(z)q ≤ Im q*G(z')q + |z - z'| ‖q‖²/(Im z Im z')`.
* `heightGrid η ρ = {η + lρ ≤ 1}`, `heightGrid_cover` (every `h ∈ [η, 1]` is within `ρ` above a
  grid height), `heightGrid_mem` (grid heights lie in `[η, 1]`), `heightGrid_card_le`.
* `count_le3`: polynomial union-bound arithmetic.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm BlockBand.Palm.CoarseRelative
open scoped ComplexConjugate

variable {N : ℕ}

theorem resolvent_quad_im_lipschitz {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {z z' : ℂ}
    (hz : 0 < z.im) (hz' : 0 < z'.im) (q : Fin N → ℂ) :
    (star q ⬝ᵥ ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im ≤
      (star q ⬝ᵥ ((H - z' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im +
        ‖z - z'‖ * nsq q / (z.im * z'.im) := by
  set R := (H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  set R' := (H - z' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  have hid := hermitian_resolvent_sub hH hz.ne' hz'.ne'
  have hsplit : star q ⬝ᵥ (R *ᵥ q) = star q ⬝ᵥ (R' *ᵥ q) +
      (z - z') * (star (Rᴴ *ᵥ q) ⬝ᵥ (R' *ᵥ q)) := by
    have e : R = R' + (z - z') • (R * R') := by rw [← hid]; abel
    have e2 : star q ⬝ᵥ ((R * R') *ᵥ q) = star (Rᴴ *ᵥ q) ⬝ᵥ (R' *ᵥ q) := by
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
        Matrix.mulVec_mulVec]
    calc star q ⬝ᵥ (R *ᵥ q) = star q ⬝ᵥ ((R' + (z - z') • (R * R')) *ᵥ q) := by rw [← e]
      _ = _ := by rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, e2,
            smul_eq_mul]
  have hRc : Rᴴ = (H - (conj z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ :=
    hermitian_resolvent_conjTranspose hH z
  have hzc : (conj z).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.2 hz.ne'
  have hb1 : l2Norm (Rᴴ *ᵥ q) ≤ l2Norm q / z.im := by
    rw [hRc]
    have := l2Norm_resolvent_le hH hzc q
    rwa [Complex.conj_im, abs_neg, abs_of_pos hz] at this
  have hb2 : l2Norm (R' *ᵥ q) ≤ l2Norm q / z'.im := by
    have := l2Norm_resolvent_le hH hz'.ne' q
    rwa [abs_of_pos hz'] at this
  have hnn : 0 ≤ nsq q := Finset.sum_nonneg fun _ _ => by positivity
  have hl2 : l2Norm q * l2Norm q = nsq q := by
    rw [l2Norm_eq_sqrt_nsq]; exact Real.mul_self_sqrt hnn
  have hCS : ‖star (Rᴴ *ᵥ q) ⬝ᵥ (R' *ᵥ q)‖ ≤ nsq q / (z.im * z'.im) := by
    refine (norm_dotProduct_le_l2 _ _).trans ?_
    calc l2Norm (Rᴴ *ᵥ q) * l2Norm (R' *ᵥ q) ≤ (l2Norm q / z.im) * (l2Norm q / z'.im) :=
          mul_le_mul hb1 hb2 (Real.sqrt_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hz.le)
      _ = nsq q / (z.im * z'.im) := by rw [← hl2]; field_simp
  rw [hsplit, Complex.add_im]
  have := Complex.im_le_norm ((z - z') * (star (Rᴴ *ᵥ q) ⬝ᵥ (R' *ᵥ q)))
  rw [norm_mul] at this
  have h2 : ‖z - z'‖ * ‖star (Rᴴ *ᵥ q) ⬝ᵥ (R' *ᵥ q)‖ ≤ ‖z - z'‖ * nsq q / (z.im * z'.im) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hCS (norm_nonneg _)
  linarith

/-- Heights `η + lρ ≤ 1`. -/
def heightGrid (η ρ : ℝ) : Finset ℝ :=
  (Finset.range (⌊(1 - η) / ρ⌋₊ + 1)).image (fun l : ℕ => η + l * ρ)

theorem heightGrid_cover {η ρ : ℝ} (hρ : 0 < ρ) {h : ℝ} (hh : η ≤ h) (h1 : h ≤ 1) :
    ∃ y ∈ heightGrid η ρ, y ≤ h ∧ h - y ≤ ρ := by
  set t := (h - η) / ρ
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hρ.le
  refine ⟨η + (⌊t⌋₊ : ℝ) * ρ, Finset.mem_image.2 ⟨⌊t⌋₊, ?_, rfl⟩, ?_, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hρ.le)
  · have := Nat.floor_le ht0
    have e : h = η + t * ρ := by simp only [t]; field_simp; ring
    nlinarith
  · have := Nat.lt_floor_add_one t
    have e : h = η + t * ρ := by simp only [t]; field_simp; ring
    nlinarith

theorem heightGrid_mem {η ρ : ℝ} (hρ : 0 < ρ) (hη1 : η ≤ 1) {y : ℝ} (hy : y ∈ heightGrid η ρ) :
    η ≤ y ∧ y ≤ 1 := by
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hy
  have hl' : (l : ℝ) ≤ (1 - η) / ρ := by
    have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    exact (Nat.cast_le.2 this).trans (Nat.floor_le (div_nonneg (by linarith) hρ.le))
  constructor
  · have : (0 : ℝ) ≤ l * ρ := by positivity
    linarith
  · have := mul_le_mul_of_nonneg_right hl' hρ.le
    rw [div_mul_cancel₀ _ hρ.ne'] at this
    linarith

theorem heightGrid_card_le {η ρ : ℝ} (hρ : 0 < ρ) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    ((heightGrid η ρ).card : ℝ) ≤ 1 / ρ + 1 := by
  have h1 : (heightGrid η ρ).card ≤ ⌊(1 - η) / ρ⌋₊ + 1 :=
    Finset.card_image_le.trans (by simp)
  have h2 : ((⌊(1 - η) / ρ⌋₊ : ℕ) : ℝ) ≤ 1 / ρ :=
    (Nat.floor_le (div_nonneg (by linarith) hρ.le)).trans
      (div_le_div_of_nonneg_right (by linarith) hρ.le)
  have : ((heightGrid η ρ).card : ℝ) ≤ ((⌊(1 - η) / ρ⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at this
  linarith

/-- Union-bound arithmetic: `T₂ G₁ G₂ N^{-(max D 0 + 4p + 2p₂ + 4)} ≤ N^{-D}/2`. -/
theorem count_le3 {N : ℕ} (hNp : (0 : ℝ) < N) (hN1 : (1 : ℝ) ≤ N) (p p₂ : ℕ) (D : ℝ)
    {T₂ G₁ G₂ : ℝ} (hT₂ : T₂ ≤ 2 ^ (4 * p) * (N : ℝ) ^ ((4 * p : ℕ) : ℝ)) (hG₁0 : 0 ≤ G₁)
    (hG₁ : G₁ ≤ (N : ℝ) ^ ((p₂ + 1 : ℕ) : ℝ)) (hG₂0 : 0 ≤ G₂)
    (hG₂ : G₂ ≤ (N : ℝ) ^ ((p₂ + 1 : ℕ) : ℝ)) (h2p : (2 : ℝ) ^ (4 * p + 1) ≤ (N : ℝ) ^ (2 : ℝ)) :
    T₂ * G₁ * G₂ * (N : ℝ) ^ (-(max D 0 + 4 * p + 2 * p₂ + 4)) ≤ (N : ℝ) ^ (-D) / 2 := by
  have hpos : 0 < (N : ℝ) ^ (-(max D 0 + 4 * p + 2 * p₂ + 4)) := Real.rpow_pos_of_pos hNp _
  have hN2 : (N : ℝ) ^ ((4 * p : ℕ) : ℝ) * (N : ℝ) ^ ((p₂ + 1 : ℕ) : ℝ) *
      (N : ℝ) ^ ((p₂ + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-(max D 0 + 4 * p + 2 * p₂ + 4)) =
      (N : ℝ) ^ (-(max D 0)) / (N : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_add hNp, ← Real.rpow_add hNp, ← Real.rpow_add hNp, ← Real.rpow_sub hNp]
    congr 1; push_cast; ring
  have hmD : (N : ℝ) ^ (-(max D 0)) ≤ (N : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_max_left D 0])
  have hN2pos : 0 < (N : ℝ) ^ (2 : ℝ) := by positivity
  have hT₂0 : T₂ * G₁ * G₂ * (N : ℝ) ^ (-(max D 0 + 4 * p + 2 * p₂ + 4)) ≤
      2 ^ (4 * p) * ((N : ℝ) ^ ((4 * p : ℕ) : ℝ) * (N : ℝ) ^ ((p₂ + 1 : ℕ) : ℝ) *
        (N : ℝ) ^ ((p₂ + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-(max D 0 + 4 * p + 2 * p₂ + 4))) := by
    rcases le_or_gt T₂ 0 with hT | hT
    · have : T₂ * G₁ * G₂ * (N : ℝ) ^ (-(max D 0 + 4 * p + 2 * p₂ + 4)) ≤ 0 := by
        have : 0 ≤ G₁ * G₂ * (N : ℝ) ^ (-(max D 0 + 4 * p + 2 * p₂ + 4)) := by positivity
        nlinarith
      exact this.trans (by positivity)
    · calc T₂ * G₁ * G₂ * (N : ℝ) ^ (-(max D 0 + 4 * p + 2 * p₂ + 4))
          ≤ (2 ^ (4 * p) * (N : ℝ) ^ ((4 * p : ℕ) : ℝ)) * (N : ℝ) ^ ((p₂ + 1 : ℕ) : ℝ) *
              (N : ℝ) ^ ((p₂ + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-(max D 0 + 4 * p + 2 * p₂ + 4)) := by
            gcongr
        _ = _ := by ring
  rw [hN2] at hT₂0
  have h2 : (2 : ℝ) ^ (4 * p) * ((N : ℝ) ^ (-(max D 0)) / (N : ℝ) ^ (2 : ℝ)) ≤
      (N : ℝ) ^ (-(max D 0)) / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ hN2pos (by norm_num)]
    have h2p' : (2 : ℝ) ^ (4 * p) * 2 ≤ (N : ℝ) ^ (2 : ℝ) := by rw [← pow_succ]; exact h2p
    have h0 : 0 ≤ (N : ℝ) ^ (-(max D 0)) := by positivity
    calc (2 : ℝ) ^ (4 * p) * (N : ℝ) ^ (-(max D 0)) * 2
        = (N : ℝ) ^ (-(max D 0)) * ((2 : ℝ) ^ (4 * p) * 2) := by ring
      _ ≤ (N : ℝ) ^ (-(max D 0)) * (N : ℝ) ^ (2 : ℝ) := mul_le_mul_of_nonneg_left h2p' h0
  linarith

end BlockBand.Palm.MomentFlow
