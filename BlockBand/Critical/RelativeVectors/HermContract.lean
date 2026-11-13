module

public import BlockBand.Palm.CoarseRelativeAlgebra

/-!
# Contraction of a Hermitian Hessian form with `Δ_j`

For a real bilinear form `B` on `ℂ^r` with `|B(v, w)| ≤ L‖v‖‖w‖` (sup norms), its Hermitian form
`q(v) = B(v, v) + B(iv, iv)`, weights `c_j` and vectors `z_j ∈ ℂ^r` such that the quadratic form
of `Δ = Σ_j c_j (z_j z_j^* - I_r)` is bounded, `|Σ_j c_j(|p^*z_j|² - ‖p‖²)| ≤ X‖p‖²` for every
`p`, `herm_contract_le`:
`|Σ_j c_j (q(z_j) - Σ_q q(e_q))| ≤ 8 r² L X`.

(`q` is the Hermitian form `v^*Kv` of `K = K(B)`, and the left side is `tr(KΔ)`; the proof
expands in the real basis `e_a, ie_a` and polarizes `Δ`.)
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Finset
open BlockBand.Palm.CoarseRelative

variable {r : ℕ}

/-- Real basis vectors `e_a`, `i e_a` of `ℂ^r`. -/
abbrev eR (a : Fin r) : Fin r → ℂ := Pi.single a 1
abbrev eI (a : Fin r) : Fin r → ℂ := Pi.single a Complex.I

theorem vec_decomp (v : Fin r → ℂ) :
    v = ∑ a, ((v a).re • eR a + (v a).im • eI a) := by
  funext q
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_eq_single q]
  · simp only [ite_true]
    rw [Complex.real_smul, Complex.real_smul, mul_one]
    exact (Complex.re_add_im (v q)).symm
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- Coordinates of a real bilinear form in the basis `e_a, ie_a`. -/
theorem bil_expand (B : (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) →L[ℝ] ℝ) (v w : Fin r → ℂ) :
    B v w = ∑ a, ∑ b, ((v a).re * (w b).re * B (eR a) (eR b) +
      (v a).re * (w b).im * B (eR a) (eI b) + (v a).im * (w b).re * B (eI a) (eR b) +
      (v a).im * (w b).im * B (eI a) (eI b)) := by
  conv_lhs => rw [vec_decomp v, vec_decomp w]
  simp only [map_sum, map_add, map_smul, _root_.sum_apply,
    add_apply, smul_apply, smul_eq_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Hermitian form `q(v) = B(v, v) + B(iv, iv)`. -/
def hermForm (B : (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) →L[ℝ] ℝ) (v : Fin r → ℂ) : ℝ :=
  B v v + B (Complex.I • v) (Complex.I • v)

/-- Coefficients `α_ab = B(e_a,e_b) + B(ie_a,ie_b)`, `β_ab = B(e_a, ie_b) - B(ie_a, e_b)`. -/
def hAlpha (B : (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) →L[ℝ] ℝ) (a b : Fin r) : ℝ :=
  B (eR a) (eR b) + B (eI a) (eI b)
def hBeta (B : (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) →L[ℝ] ℝ) (a b : Fin r) : ℝ :=
  B (eR a) (eI b) - B (eI a) (eR b)

theorem hermForm_expand (B : (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) →L[ℝ] ℝ) (v : Fin r → ℂ) :
    hermForm B v = ∑ a, ∑ b, ((starRingEnd ℂ (v a) * v b).re * hAlpha B a b +
      (starRingEnd ℂ (v a) * v b).im * hBeta B a b) := by
  unfold hermForm
  rw [bil_expand B v v, bil_expand B (Complex.I • v) (Complex.I • v), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, hAlpha, hBeta]
  ring

theorem hermForm_basis (B : (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) →L[ℝ] ℝ) (q : Fin r) :
    hermForm B (eR q) = hAlpha B q q := by
  rw [hermForm_expand, Finset.sum_eq_single q, Finset.sum_eq_single q]
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro a _ ha; refine Finset.sum_eq_zero fun b _ => ?_; simp [Pi.single_apply, ha]
  · simp

/-- `|B(e,e')| ≤ L` on the real basis. -/
theorem norm_eR (a : Fin r) : ‖eR a‖ = 1 := by
  rw [Pi.norm_single]; simp
theorem norm_eI (a : Fin r) : ‖eI a‖ = 1 := by
  rw [Pi.norm_single]; simp

theorem abs_hAlpha_le {B : (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) →L[ℝ] ℝ} {L : ℝ}
    (hB : ∀ v w, |B v w| ≤ L * ‖v‖ * ‖w‖) (a b : Fin r) : |hAlpha B a b| ≤ 2 * L := by
  have h1 := hB (eR a) (eR b)
  have h2 := hB (eI a) (eI b)
  rw [norm_eR, norm_eR] at h1
  rw [norm_eI, norm_eI] at h2
  unfold hAlpha
  calc _ ≤ |B (eR a) (eR b)| + |B (eI a) (eI b)| := abs_add_le _ _
    _ ≤ L * 1 * 1 + L * 1 * 1 := add_le_add h1 h2
    _ = 2 * L := by ring

theorem abs_hBeta_le {B : (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) →L[ℝ] ℝ} {L : ℝ}
    (hB : ∀ v w, |B v w| ≤ L * ‖v‖ * ‖w‖) (a b : Fin r) : |hBeta B a b| ≤ 2 * L := by
  have h1 := hB (eR a) (eI b)
  have h2 := hB (eI a) (eR b)
  rw [norm_eR, norm_eI] at h1
  rw [norm_eI, norm_eR] at h2
  unfold hBeta
  calc _ ≤ |B (eR a) (eI b)| + |B (eI a) (eR b)| := abs_sub _ _
    _ ≤ L * 1 * 1 + L * 1 * 1 := add_le_add h1 h2
    _ = 2 * L := by ring

/-!
## Polarization of `Δ`
-/

section Polar

variable {ι : Type*} (s : Finset ι) (c : ι → ℝ) (z : ι → Fin r → ℂ)

/-- `P(p) = Σ_j c_j (|p^*z_j|² - ‖p‖²)`. -/
def polQ (p : Fin r → ℂ) : ℝ := ∑ j ∈ s, c j * (‖star p ⬝ᵥ z j‖ ^ 2 - nsq p)

theorem star_eR_dot (a : Fin r) (x : Fin r → ℂ) : star (eR a) ⬝ᵥ x = x a := by
  simp [dotProduct, Pi.single_apply]

theorem star_eRI_dot (a b : Fin r) (u : ℂ) (x : Fin r → ℂ) :
    star (eR a + u • eR b) ⬝ᵥ x = x a + starRingEnd ℂ u * x b := by
  simp only [dotProduct, Pi.star_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add,
    star_mul', Pi.single_apply, add_mul, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', mul_comm]

theorem nsq_eR (a : Fin r) : nsq (eR a) = 1 := by
  unfold nsq
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem nsq_eRI {a b : Fin r} (hab : a ≠ b) {u : ℂ} (hu : ‖u‖ = 1) :
    nsq (eR a + u • eR b) = 2 := by
  unfold nsq
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩)]
  have h0 : ∑ x ∈ (univ.erase a).erase b, ‖(eR a + u • eR b) x‖ ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxa : x ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
    have hxb : x ≠ b := Finset.ne_of_mem_erase hx
    simp [hxa, hxb]
  rw [h0]
  simp [hab, Ne.symm hab, hu]
  norm_num

theorem norm_sq_add (x y : ℂ) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 +
    2 * (starRingEnd ℂ x * y).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_add]
  simp [Complex.mul_re]

/-- Diagonal entries: `Σ_j c_j (|z_ja|² - 1) = P(e_a)`. -/
theorem polQ_eR (a : Fin r) : polQ s c z (eR a) =
    ∑ j ∈ s, c j * ((starRingEnd ℂ (z j a) * z j a).re - 1) := by
  unfold polQ
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_eR_dot, nsq_eR, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Off-diagonal polarization: `P(e_a + u e_b) = P(e_a) + P(e_b) + 2Σ_j c_j Re(conj(z_ja) ū z_jb)`. -/
theorem polQ_eRI {a b : Fin r} (hab : a ≠ b) {u : ℂ} (hu : ‖u‖ = 1) :
    polQ s c z (eR a + u • eR b) = polQ s c z (eR a) + polQ s c z (eR b) +
      2 * ∑ j ∈ s, c j * (starRingEnd ℂ (z j a) * (starRingEnd ℂ u * z j b)).re := by
  unfold polQ
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_eRI_dot a b, nsq_eRI hab hu, star_eR_dot, star_eR_dot, nsq_eR, nsq_eR, norm_sq_add,
    norm_mul, Complex.norm_conj, hu]
  ring

end Polar

/-- **Contraction of the Hermitian form with `Δ`.** See the module docstring. -/
theorem herm_contract_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (z : ι → Fin r → ℂ)
    {B : (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) →L[ℝ] ℝ} {L X : ℝ}
    (hB : ∀ v w, |B v w| ≤ L * ‖v‖ * ‖w‖) (hL : 0 ≤ L)
    (hX : ∀ p : Fin r → ℂ, |∑ j ∈ s, c j * (‖star p ⬝ᵥ z j‖ ^ 2 - nsq p)| ≤ X * nsq p) :
    |∑ j ∈ s, c j * (hermForm B (z j) - ∑ q : Fin r, hermForm B (eR q))| ≤
      8 * (r : ℝ) ^ 2 * L * X := by
  -- the matrix entries of `Δ`
  set R : Fin r → Fin r → ℝ := fun a b => ∑ j ∈ s, c j *
    ((starRingEnd ℂ (z j a) * z j b).re - if a = b then 1 else 0) with hR
  set Im' : Fin r → Fin r → ℝ := fun a b => ∑ j ∈ s, c j *
    (starRingEnd ℂ (z j a) * z j b).im with hIm
  have hexp : ∑ j ∈ s, c j * (hermForm B (z j) - ∑ q : Fin r, hermForm B (eR q)) =
      ∑ a, ∑ b, (hAlpha B a b * R a b + hBeta B a b * Im' a b) := by
    have htr : ∑ q : Fin r, hermForm B (eR q) =
        ∑ a, ∑ b, (if a = b then (1 : ℝ) else 0) * hAlpha B a b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hermForm_basis, Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    have hj : ∀ j, c j * (hermForm B (z j) - ∑ q : Fin r, hermForm B (eR q)) =
        ∑ a, ∑ b, (c j * ((starRingEnd ℂ (z j a) * z j b).re - if a = b then 1 else 0) *
          hAlpha B a b + c j * (starRingEnd ℂ (z j a) * z j b).im * hBeta B a b) := by
      intro j
      rw [hermForm_expand, htr, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    simp_rw [hj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hR, hIm, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- entry bounds by polarization
  have hRb : ∀ a b, |R a b| ≤ 2 * X := by
    intro a b
    by_cases hab : a = b
    · subst hab
      have h : |polQ s c z (eR a)| ≤ X * nsq (eR a) := hX (eR a)
      rw [nsq_eR, polQ_eR] at h
      have : R a a = ∑ j ∈ s, c j * ((starRingEnd ℂ (z j a) * z j a).re - 1) := by
        simp [hR]
      rw [this]
      have hX0 : 0 ≤ X := by linarith [abs_nonneg (∑ j ∈ s, c j * ((starRingEnd ℂ (z j a) * z j a).re - 1))]
      linarith
    · have h1 : |polQ s c z (eR a + (1 : ℂ) • eR b)| ≤ X * nsq (eR a + (1 : ℂ) • eR b) :=
        hX (eR a + (1 : ℂ) • eR b)
      have h2 : |polQ s c z (eR a)| ≤ X * nsq (eR a) := hX (eR a)
      have h3 : |polQ s c z (eR b)| ≤ X * nsq (eR b) := hX (eR b)
      rw [nsq_eRI hab (by simp), polQ_eRI s c z hab (by simp)] at h1
      rw [nsq_eR] at h2 h3
      have hRe : R a b = ∑ j ∈ s, c j * (starRingEnd ℂ (z j a) * (starRingEnd ℂ 1 * z j b)).re := by
        simp [hR, hab]
      rw [hRe]
      rw [abs_le] at h1 h2 h3 ⊢
      constructor <;> linarith
  have hIb : ∀ a b, |Im' a b| ≤ 2 * X := by
    intro a b
    by_cases hab : a = b
    · subst hab
      have h := hX (eR a)
      rw [nsq_eR] at h
      have : Im' a a = 0 := by
        simp only [hIm]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_im, mul_zero]
      rw [this, abs_zero]
      linarith [abs_nonneg (∑ j ∈ s, c j * (‖star (eR a) ⬝ᵥ z j‖ ^ 2 - 1))]
    · have h1 : |polQ s c z (eR a + Complex.I • eR b)| ≤ X * nsq (eR a + Complex.I • eR b) :=
        hX (eR a + Complex.I • eR b)
      have h2 : |polQ s c z (eR a)| ≤ X * nsq (eR a) := hX (eR a)
      have h3 : |polQ s c z (eR b)| ≤ X * nsq (eR b) := hX (eR b)
      rw [nsq_eRI hab (by simp), polQ_eRI s c z hab (by simp)] at h1
      rw [nsq_eR] at h2 h3
      have hIe : Im' a b = ∑ j ∈ s, c j *
          (starRingEnd ℂ (z j a) * (starRingEnd ℂ Complex.I * z j b)).re := by
        simp only [hIm]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        simp [Complex.mul_re, Complex.mul_im]
        ring
      rw [hIe]
      rw [abs_le] at h1 h2 h3 ⊢
      constructor <;> linarith
  rw [hexp]
  calc |∑ a, ∑ b, (hAlpha B a b * R a b + hBeta B a b * Im' a b)|
      ≤ ∑ a, ∑ b, |hAlpha B a b * R a b + hBeta B a b * Im' a b| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _a : Fin r, ∑ _b : Fin r, (8 * L * X) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        have h1 := mul_le_mul (abs_hAlpha_le hB a b) (hRb a b) (abs_nonneg _) (by linarith)
        have h2 := mul_le_mul (abs_hBeta_le hB a b) (hIb a b) (abs_nonneg _) (by linarith)
        linarith
    _ = 8 * (r : ℝ) ^ 2 * L * X := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end BlockBand.Critical.RelativeVectors
