module

public import BlockBand.Critical.RelativeVectors.DysonShift

/-!
# Polarization in the frame

Deterministic linear algebra: the coarse relative law is applied polarized in `V`.

* `polFrame V`: the `4r²` vectors `V(e_a + c e_b)`, `c ∈ {1, -1, i, -i}` (the family `Q` to which
  `CoarseRelativeContract` is applied; `polFrame_card_le`).
* `polarization`: `4 x^*Ay = q(x+y) - q(x-y) - i q(x+iy) + i q(x-iy)`, `q(v) = v^*Av`.
* `frame_quad_le_of_pol`: if `|q^*Aq| ≤ β` on `polFrame V`, then `|(Vp)^*A(Vp)| ≤ β r ‖p‖²`
  for every `p ∈ ℂ^r`.
* `quadForm_polFrame_le`: `q^*Γq ≤ 4` on `polFrame V` when `V^*ΓV = I_r`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.MomentFlow BlockBand.Palm.CoarseRelative
open scoped ComplexConjugate

variable {N r : ℕ}

/-- The polarization coefficients `1, -1, i, -i`. -/
def polCoeff : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

/-- The polarization family `V(e_a + c e_b)` of a frame. -/
def polFrame (V : Matrix (Fin N) (Fin r) ℂ) : Finset (Fin N → ℂ) :=
  Finset.univ.image fun t : Fin r × Fin r × Fin 4 =>
    V *ᵥ (Pi.single t.1 1 + polCoeff t.2.2 • Pi.single t.2.1 1)

theorem polFrame_card_le (V : Matrix (Fin N) (Fin r) ℂ) : ((polFrame V).card : ℝ) ≤ 4 * r ^ 2 := by
  unfold polFrame
  have h := (Finset.card_image_le (s := (Finset.univ : Finset (Fin r × Fin r × Fin 4)))
    (f := fun t : Fin r × Fin r × Fin 4 =>
      V *ᵥ (Pi.single t.1 1 + polCoeff t.2.2 • Pi.single t.2.1 (1 : ℂ))))
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin] at h
  have : ((r * (r * 4) : ℕ) : ℝ) = 4 * r ^ 2 := by push_cast; ring
  rw [← this]
  exact_mod_cast h

theorem quad_add_smul (A : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) (c : ℂ) :
    star (x + c • y) ⬝ᵥ (A *ᵥ (x + c • y)) =
      star x ⬝ᵥ (A *ᵥ x) + c * (star x ⬝ᵥ (A *ᵥ y)) + conj c * (star y ⬝ᵥ (A *ᵥ x)) +
        conj c * c * (star y ⬝ᵥ (A *ᵥ y)) := by
  rw [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    dotProduct_add, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul, Complex.star_def]
  ring

/-- **Polarization.** -/
theorem polarization (A : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) :
    4 * (star x ⬝ᵥ (A *ᵥ y)) =
      star (x + (1 : ℂ) • y) ⬝ᵥ (A *ᵥ (x + (1 : ℂ) • y)) -
        star (x + (-1 : ℂ) • y) ⬝ᵥ (A *ᵥ (x + (-1 : ℂ) • y)) -
        Complex.I * star (x + Complex.I • y) ⬝ᵥ (A *ᵥ (x + Complex.I • y)) +
        Complex.I * star (x + (-Complex.I) • y) ⬝ᵥ (A *ᵥ (x + (-Complex.I) • y)) := by
  rw [quad_add_smul, quad_add_smul, quad_add_smul, quad_add_smul]
  simp only [map_one, map_neg, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_bilin_le_of_pol (A : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) {β : ℝ}
    (hβ : ∀ k : Fin 4, ‖star (x + polCoeff k • y) ⬝ᵥ (A *ᵥ (x + polCoeff k • y))‖ ≤ β) :
    ‖star x ⬝ᵥ (A *ᵥ y)‖ ≤ β := by
  have h := polarization A x y
  have h0 := hβ 0
  have h1 := hβ 1
  have h2 := hβ 2
  have h3 := hβ 3
  rw [show polCoeff 0 = 1 from rfl] at h0
  rw [show polCoeff 1 = -1 from rfl] at h1
  rw [show polCoeff 2 = Complex.I from rfl] at h2
  rw [show polCoeff 3 = -Complex.I from rfl] at h3
  have h4 : ‖(4 : ℂ) * (star x ⬝ᵥ (A *ᵥ y))‖ ≤ 4 * β := by
    rw [h]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
    linarith
  rw [norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num] at h4
  linarith

theorem mulVec_eq_sum_single (V : Matrix (Fin N) (Fin r) ℂ) (p : Fin r → ℂ) :
    V *ᵥ p = ∑ b, p b • (V *ᵥ Pi.single b 1) := by
  conv_lhs => rw [show p = ∑ b, p b • Pi.single b (1 : ℂ) by
    ext i; simp [Finset.sum_apply, Pi.single_apply]]
  rw [mulVec_sum]
  simp only [mulVec_smul]

/-- **Frame bound from the polarization family.** -/
theorem frame_quad_le_of_pol (V : Matrix (Fin N) (Fin r) ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    {β : ℝ} (hβ : ∀ q ∈ polFrame V, ‖star q ⬝ᵥ (A *ᵥ q)‖ ≤ β) (p : Fin r → ℂ) :
    ‖star (V *ᵥ p) ⬝ᵥ (A *ᵥ (V *ᵥ p))‖ ≤ β * r * nsq p := by
  set v : Fin r → Fin N → ℂ := fun b => V *ᵥ Pi.single b 1 with hv
  have hab : ∀ a b, ‖star (v a) ⬝ᵥ (A *ᵥ v b)‖ ≤ β := by
    intro a b
    refine norm_bilin_le_of_pol A (v a) (v b) fun k => ?_
    have hmem : V *ᵥ (Pi.single a 1 + polCoeff k • Pi.single b 1) ∈ polFrame V :=
      Finset.mem_image.2 ⟨(a, b, k), Finset.mem_univ _, rfl⟩
    have e : v a + polCoeff k • v b = V *ᵥ (Pi.single a 1 + polCoeff k • Pi.single b 1) := by
      rw [mulVec_add, mulVec_smul]
    rw [e]
    exact hβ _ hmem
  have hβ0 : 0 ≤ β ∨ r = 0 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · exact Or.inr hr
    · exact Or.inl ((norm_nonneg _).trans (hab ⟨0, hr⟩ ⟨0, hr⟩))
  rw [mulVec_eq_sum_single]
  have hexp : star (∑ b, p b • v b) ⬝ᵥ (A *ᵥ ∑ b, p b • v b) =
      ∑ a, ∑ b, conj (p a) * p b * (star (v a) ⬝ᵥ (A *ᵥ v b)) := by
    rw [star_sum, mulVec_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      Complex.star_def]
    ring
  rw [hexp]
  rcases hβ0 with hβ0 | hr
  · calc ‖∑ a, ∑ b, conj (p a) * p b * (star (v a) ⬝ᵥ (A *ᵥ v b))‖
        ≤ ∑ a, ∑ b, ‖p a‖ * ‖p b‖ * β := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left (hab a b) (by positivity)
      _ = β * (∑ a, ‖p a‖) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ β * (r * nsq p) := by
          apply mul_le_mul_of_nonneg_left _ hβ0
          have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a : Fin r => ‖p a‖)
          simpa [nsq, Finset.card_univ, Fintype.card_fin] using this
      _ = β * r * nsq p := by ring
  · subst hr
    simp [nsq]

theorem quadForm_polFrame_le {Γ : Matrix (Fin N) (Fin N) ℂ} {V : Matrix (Fin N) (Fin r) ℂ}
    (hV : Vᴴ * Γ * V = 1) {q : Fin N → ℂ} (hq : q ∈ polFrame V) : quadForm Γ q ≤ 4 := by
  obtain ⟨⟨a, b, k⟩, -, rfl⟩ := Finset.mem_image.1 hq
  rw [quadForm_frame hV]
  have hc : ‖polCoeff k‖ = 1 := by
    fin_cases k <;> simp [polCoeff]
  set u : Fin r → ℂ := Pi.single a 1 + polCoeff k • Pi.single b 1
  have hsq : ∀ i, ‖u i‖ ^ 2 ≤ 2 * ‖(Pi.single a (1 : ℂ) : Fin r → ℂ) i‖ ^ 2 +
      2 * ‖(polCoeff k • (Pi.single b (1 : ℂ) : Fin r → ℂ)) i‖ ^ 2 := by
    intro i
    have h := norm_add_le ((Pi.single a (1 : ℂ) : Fin r → ℂ) i)
      ((polCoeff k • (Pi.single b (1 : ℂ) : Fin r → ℂ)) i)
    have h0 := norm_nonneg (u i)
    have : u i = (Pi.single a (1 : ℂ) : Fin r → ℂ) i +
        (polCoeff k • (Pi.single b (1 : ℂ) : Fin r → ℂ)) i := rfl
    rw [this] at h0 ⊢
    nlinarith [sq_nonneg (‖(Pi.single a (1 : ℂ) : Fin r → ℂ) i‖ -
      ‖(polCoeff k • (Pi.single b (1 : ℂ) : Fin r → ℂ)) i‖)]
  have h1 : nsq (Pi.single a (1 : ℂ) : Fin r → ℂ) = 1 := by
    unfold nsq
    rw [Finset.sum_eq_single a (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have h2 : nsq (polCoeff k • (Pi.single b (1 : ℂ) : Fin r → ℂ)) = 1 := by
    unfold nsq
    rw [Finset.sum_eq_single b (fun j _ hj => by simp [hj]) (by simp)]
    simp [hc]
  calc nsq u = ∑ i, ‖u i‖ ^ 2 := rfl
    _ ≤ ∑ i, (2 * ‖(Pi.single a (1 : ℂ) : Fin r → ℂ) i‖ ^ 2 +
          2 * ‖(polCoeff k • (Pi.single b (1 : ℂ) : Fin r → ℂ)) i‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hsq i
    _ = 2 * nsq (Pi.single a (1 : ℂ) : Fin r → ℂ) +
          2 * nsq (polCoeff k • (Pi.single b (1 : ℂ) : Fin r → ℂ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; rfl
    _ = 4 := by rw [h1, h2]; norm_num

end BlockBand.Critical.RelativeVectors
