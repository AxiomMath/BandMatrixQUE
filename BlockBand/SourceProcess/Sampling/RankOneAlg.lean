module

public import BlockBand.SourceProcess.SourceProcessLaw.Sampling

/-!
# The sampled rank-one matrices: algebra

* `tagEmb W n k` (`T_k`): the embedding `ℂ^W → ℂ^{n×W}` on the block of birth index `k`;
  `tagVector_eq`: `ι_k g = T_k g`; `tagEmb_mul_conjTranspose`: `T_k T_k* = P_k`.
* `rankOne U κ (k, g) = κ (U* ι_k g)(U* ι_k g)*`, `rankOne_psd`.
* `trace_mul_rankOne`: `Re Tr(K ξ) = κ Re(g* S*KS g)`, `S = U* T_k` (a quadratic form in `g`);
  `trace_rankOne`: `Re Tr ξ = κ Σ_a |(S g)_a|²`; `sum_normSq_tagS`: `Σ |S_{ay}|² = Re Tr(U* P_k U)`;
  `tagS_mul_conjTranspose`: `S S* = U* P_k U`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Sampling

open Matrix BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.SourceProcessLaw
open scoped ComplexConjugate ComplexOrder

variable {W n : ℕ}

/-- `T_k`: `ℂ^W` placed on the block of birth index `k` (position `n-1-k`). -/
def tagEmb (W n k : ℕ) : Matrix (Fin n × Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => if k < n ∧ x.1.val = n - 1 - k ∧ x.2 = y then 1 else 0

theorem tagVector_eq (k : ℕ) (g : Fin W → ℂ) : tagVector W n k g = tagEmb W n k *ᵥ g := by
  funext x
  simp only [tagVector, tagEmb, mulVec, dotProduct, of_apply]
  by_cases h : k < n ∧ x.1.val = n - 1 - k
  · obtain ⟨h1, h2⟩ := h
    simp [h1, h2]
  · rw [ite_eq_right h]
    refine (Finset.sum_eq_zero fun y _ => ?_).symm
    rw [ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩, zero_mul]

theorem tagEmb_mul_conjTranspose (k : ℕ) :
    tagEmb W n k * (tagEmb W n k)ᴴ = tagProjection W n k := by
  ext x x'
  simp only [mul_apply, conjTranspose_apply, tagEmb, of_apply, tagProjection, diagonal_apply]
  by_cases hx : k < n ∧ x.1.val = n - 1 - k
  · by_cases hx' : k < n ∧ x'.1.val = n - 1 - k
    · have e : ∀ y : Fin W, ((if k < n ∧ x.1.val = n - 1 - k ∧ x.2 = y then (1 : ℂ) else 0) *
          star (if k < n ∧ x'.1.val = n - 1 - k ∧ x'.2 = y then (1 : ℂ) else 0)) =
          if x'.2 = y then (if x.2 = x'.2 then 1 else 0) else 0 := fun y => by
        by_cases h1 : x'.2 = y
        · subst h1; by_cases h2 : x.2 = x'.2 <;> simp [hx, hx', h2]
        · simp [hx', h1]
      rw [Finset.sum_congr rfl fun y _ => e y, Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ite_true]
      have hxx : x.1 = x'.1 := Fin.ext (hx.2.trans hx'.2.symm)
      by_cases h2 : x.2 = x'.2
      · have : x = x' := Prod.ext hxx h2
        simp [this, hx']
      · have : x ≠ x' := fun h => h2 (by rw [h])
        simp [this, h2]
    · have hne : x ≠ x' := fun h => hx' (h ▸ hx)
      rw [ite_eq_right hne]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [ite_eq_right (c := k < n ∧ x'.1.val = n - 1 - k ∧ x'.2 = y)
        (fun h' => hx' ⟨h'.1, h'.2.1⟩), star_zero, mul_zero]
  · rw [Finset.sum_eq_zero fun y _ => by rw [ite_eq_right fun h' => hx ⟨h'.1, h'.2.1⟩, zero_mul]]
    by_cases hxx : x = x'
    · subst hxx; simp [hx]
    · simp [hxx]

/-- One sampled injection `κ v v*`, `v = U* ι_k g`. -/
def rankOne (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (κ : ℝ) (y : ℕ × (Fin W → ℂ)) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (κ : ℂ) • vecMulVec (Uᴴ *ᵥ tagVector W n y.1 y.2) (star (Uᴴ *ᵥ tagVector W n y.1 y.2))

theorem rankOne_psd (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) {κ : ℝ} (hκ : 0 ≤ κ)
    (y : ℕ × (Fin W → ℂ)) : (rankOne U κ y).PosSemidef :=
  (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast hκ)

/-- `S = U* T_k`. -/
abbrev tagS (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (k : ℕ) :
    Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  Uᴴ * tagEmb W n k

theorem rankOne_eq (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (κ : ℝ) (k : ℕ)
    (g : Fin W → ℂ) :
    rankOne U κ (k, g) = (κ : ℂ) • vecMulVec (tagS U k *ᵥ g) (star (tagS U k *ᵥ g)) := by
  simp only [rankOne, tagVector_eq, mulVec_mulVec]

theorem tagS_mul_conjTranspose (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (k : ℕ) :
    tagS U k * (tagS U k)ᴴ = Uᴴ * tagProjection W n k * U := by
  rw [tagS, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (tagEmb W n k), tagEmb_mul_conjTranspose, ← Matrix.mul_assoc]

theorem trace_mul_vecMulVec {m : Type*} [Fintype m] (K : Matrix m m ℂ) (v : m → ℂ) :
    (K * vecMulVec v (star v)).trace = star v ⬝ᵥ (K *ᵥ v) := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum,
    Pi.star_apply]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem dot_quad {m : Type*} [Fintype m] (B : Matrix m m ℂ) (g : m → ℂ) :
    star g ⬝ᵥ (B *ᵥ g) = ∑ a, ∑ b, conj (g a) * B a b * g b := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- `Re Tr(K ξ) = κ Re(g* (S*KS) g)`. -/
theorem trace_mul_rankOne (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (κ : ℝ)
    (K : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (k : ℕ) (g : Fin W → ℂ) :
    (K * rankOne U κ (k, g)).trace.re =
      κ * (∑ a, ∑ b, conj (g a) * ((tagS U k)ᴴ * K * tagS U k) a b * g b).re := by
  rw [rankOne_eq, Matrix.mul_smul, trace_smul, trace_mul_vecMulVec, star_mulVec,
    ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← dot_quad, smul_eq_mul,
    Complex.re_ofReal_mul, Matrix.mul_assoc]

/-- `Tr(S* K S) = Tr(K U* P_k U)`. -/
theorem trace_tagS (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ)
    (K : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (k : ℕ) :
    ((tagS U k)ᴴ * K * tagS U k).trace = (K * (Uᴴ * tagProjection W n k * U)).trace := by
  rw [← tagS_mul_conjTranspose, trace_mul_comm, ← Matrix.mul_assoc, trace_mul_comm,
    Matrix.mul_assoc]

/-- `Re Tr ξ = κ Σ_a |(S g)_a|²`. -/
theorem trace_rankOne (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (κ : ℝ) (k : ℕ)
    (g : Fin W → ℂ) :
    (rankOne U κ (k, g)).trace.re = κ * ∑ a, ‖(tagS U k *ᵥ g) a‖ ^ 2 := by
  rw [rankOne_eq, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  congr 1
  simp only [trace, diag, vecMulVec_apply, Pi.star_apply, Complex.re_sum, Complex.star_def,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- `Σ_{a,y} |S_{ay}|² = Re Tr(U* P_k U)`. -/
theorem sum_normSq_tagS (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (k : ℕ) :
    ∑ a, ∑ y, ‖tagS U k a y‖ ^ 2 = (Uᴴ * tagProjection W n k * U).trace.re := by
  rw [← tagS_mul_conjTranspose]
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum, Complex.star_def,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

end BlockBand.SourceProcess.Sampling
