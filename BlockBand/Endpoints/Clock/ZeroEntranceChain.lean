module

public import BlockBand.Endpoints.Clock.ZeroEntranceDecay
public import BlockBand.Internal.Contracts.Layers

/-!
# The zero-entrance lemma: the finite chain and the seed estimate

We prove the decay estimate (the finite seed bound) for the finite Dyson chain with zero boundary
(Steps 2–7 of the paper's proof of the zero-entrance lemma). The argument is deterministic. The
matched value and port are `Layers.matchedA` and `Layers.boundaryZ`: `a = (-e - i√(4-e²))/2`
(`Im a < 0`, `|a| = 1`) and `z = a⁻¹ + b a` (`Im z = (1-b)√(4-e²)/2 > 0`).

## The chain (`IsZeroEntranceChain b e J m`)

`m : ℕ → ℂ` with `m 0 = 0`, `Im m_ℓ < 0` for `1 ≤ ℓ ≤ J+1`,
`m_ℓ⁻¹ = -e - c m_ℓ - b m_{ℓ-1} - b m_{ℓ+1}` for `1 ≤ ℓ ≤ J` (`c = 1 - 2b`), and
`m_{J+1}⁻¹ = z - b m_J`.

## Results (uniform in `J` and in the compact parameter set)

The compact parameter set is `κ ≤ b`, `κ ≤ 1 - 2b`, `κ ≤ 4 - e²` for a fixed `κ > 0`
(every compact subset of `{0 < b < 1/2} × (-2,2)` lies in one of these).
* Step 4 (`zeroEntrance_bounds`): `r_κ ≤ |m_ℓ| ≤ R_κ` for `1 ≤ ℓ ≤ J+1`.
* Step 5 (`zeroEntrance_spectrum`): the symmetrized matrix `A = R_m S R_m`,
  `R_m = diag(√|m_ℓ|)`, satisfies `xᵀAx ≤ |x|²` and `|x|² + xᵀAx ≥ δ_κ |x|²` for every real `x`,
  i.e. `Spec A ⊂ [-1 + δ_κ, 1]`. (Proved by a Schur-type identity with the subinvariant vector
  `φ = R_m⁻¹ √y`, instead of an eigenvector argument for the lower end.)
* Step 6 (`zeroEntrance_singular_lower`): `|(I - ΘA)x| ≥ κ₀ |x|`, `Θ = diag(a m_ℓ/|m_ℓ|)`.
* Step 7 (`zeroEntrance_finite_seed`, the finite seed bound):
  `|m_{J+1} - a| ≤ C_κ e^{-c_κ J}`.

The limiting measures, the identification of their Stieltjes transforms with `m_{J+1}`, and the
concentration and perturbation in the initial matrix are handled in the proof of `zeroEntrance_of`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Complex BlockBand.Internal.Contracts.Layers

/-- The finite chain the finite Dyson equation with zero boundary `m₀ = 0`,
`c = 1 - 2b`, port parameter `z = boundaryZ b e`, and negative imaginary parts. -/
structure IsZeroEntranceChain (b e : ℝ) (J : ℕ) (m : ℕ → ℂ) : Prop where
  zero : m 0 = 0
  im_neg : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ J + 1 → (m ℓ).im < 0
  bulk : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ J →
    (m ℓ)⁻¹ = -(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * m ℓ - b * m (ℓ - 1) - b * m (ℓ + 1)
  port : (m (J + 1))⁻¹ = boundaryZ b e - b * m J

namespace ZeroEntrance

/-!
## The tridiagonal matrix `S` on sites `1, …, J+1` (zero-based positions `0, …, J`)
-/

/-- `S_kl`: diagonal `c = 1 - 2b` on the first `J` sites, `0` at the port, `b` on the
off-diagonals. Positions are zero-based (`k` is site `k + 1`). -/
def chainS (b : ℝ) (J k l : ℕ) : ℝ :=
  (if l = k then (if k < J then 1 - 2 * b else 0) else 0) + (if l = k + 1 then b else 0) +
    (if k = l + 1 then b else 0)

theorem chainS_symm (b : ℝ) (J k l : ℕ) : chainS b J k l = chainS b J l k := by
  unfold chainS
  by_cases h : l = k
  · subst h; rfl
  · have h' : k ≠ l := Ne.symm h
    simp only [h, h', ite_false]
    ring

theorem chainS_nonneg {b : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b) (J k l : ℕ) :
    0 ≤ chainS b J k l := by
  unfold chainS
  have h1 : 0 ≤ (if l = k then (if k < J then 1 - 2 * b else 0) else 0) := by
    split_ifs <;> linarith
  have h2 : 0 ≤ (if l = k + 1 then b else 0) := by split_ifs <;> linarith
  have h3 : 0 ≤ (if k = l + 1 then b else 0) := by split_ifs <;> linarith
  linarith

theorem chainS_tri {b : ℝ} {J k l : ℕ} (h : chainS b J k l ≠ 0) : k ≤ l + 1 ∧ l ≤ k + 1 := by
  by_contra hc
  apply h
  unfold chainS
  have h1 : l ≠ k := by omega
  have h2 : l ≠ k + 1 := by omega
  have h3 : k ≠ l + 1 := by omega
  simp [h1, h2, h3]

theorem chainS_diag (b : ℝ) (J k : ℕ) :
    chainS b J k k = if k < J then 1 - 2 * b else 0 := by
  unfold chainS; simp

/-- The row action of `S` on a vector `f (l + 1)` with `f 0 = 0`. -/
theorem sum_chainS {J : ℕ} (b : ℝ) (f : ℕ → ℂ) (hf : f 0 = 0) (k : Fin (J + 1)) :
    ∑ l : Fin (J + 1), (chainS b J k l : ℂ) * f (l + 1) =
      (if (k : ℕ) < J then ((1 - 2 * b : ℝ) : ℂ) * f (k + 1) + b * f (k + 2) else 0) +
        b * f k := by
  rw [Fin.sum_univ_eq_sum_range (fun l => (chainS b J k l : ℂ) * f (l + 1)) (J + 1)]
  have hpt : ∀ x : ℕ, (chainS b J k x : ℂ) * f (x + 1) =
      (if x = (k : ℕ) then (if (k : ℕ) < J then ((1 : ℂ) - 2 * b) else 0) * f (x + 1) else 0) +
      (if x = (k : ℕ) + 1 then (b : ℂ) * f (x + 1) else 0) +
      (if (k : ℕ) = x + 1 then (b : ℂ) * f (x + 1) else 0) := by
    intro x
    unfold chainS
    split_ifs <;> push_cast <;> ring
  simp only [hpt, Finset.sum_add_distrib]
  have hk : (k : ℕ) < J + 1 := k.2
  have e1 : ∑ x ∈ Finset.range (J + 1),
      (if x = (k : ℕ) then (if (k : ℕ) < J then ((1 : ℂ) - 2 * b) else 0) * f (x + 1) else 0) =
      (if (k : ℕ) < J then ((1 : ℂ) - 2 * b) else 0) * f (k + 1) := by
    rw [Finset.sum_ite_eq']; simp [hk]
  have e2 : ∑ x ∈ Finset.range (J + 1), (if x = (k : ℕ) + 1 then (b : ℂ) * f (x + 1) else 0) =
      if (k : ℕ) < J then (b : ℂ) * f (k + 2) else 0 := by
    rw [Finset.sum_ite_eq']
    by_cases h : (k : ℕ) < J
    · simp [h, show (k : ℕ) + 1 < J + 1 by omega]
    · simp [h, show ¬ ((k : ℕ) + 1 < J + 1) by omega]
  have e3 : ∑ x ∈ Finset.range (J + 1), (if (k : ℕ) = x + 1 then (b : ℂ) * f (x + 1) else 0) =
      (b : ℂ) * f k := by
    rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | hpos
    · rw [h0, hf, mul_zero]
      exact Finset.sum_eq_zero fun x _ => by simp
    · obtain ⟨k', hk'⟩ : ∃ k', (k : ℕ) = k' + 1 := ⟨(k : ℕ) - 1, by omega⟩
      rw [hk']
      have : ∀ x, (k' + 1 = x + 1) ↔ (k' = x) := fun x => by omega
      simp only [this]
      rw [Finset.sum_ite_eq]
      simp [show k' < J + 1 by omega]
  rw [e1, e2, e3]
  split_ifs <;> push_cast <;> ring

/-!
## The matched value
-/

theorem matchedA_re (e : ℝ) : (matchedA e).re = -e / 2 := rfl
theorem matchedA_im (e : ℝ) : (matchedA e).im = -Real.sqrt (4 - e ^ 2) / 2 := rfl

theorem matchedA_normSq {e : ℝ} (he : e ^ 2 ≤ 4) : Complex.normSq (matchedA e) = 1 := by
  rw [Complex.normSq_apply, matchedA_re, matchedA_im]
  have := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 4 - e ^ 2)
  nlinarith

theorem matchedA_norm {e : ℝ} (he : e ^ 2 ≤ 4) : ‖matchedA e‖ = 1 := by
  rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, matchedA_normSq he, Real.sqrt_one]

theorem matchedA_ne_zero {e : ℝ} (he : e ^ 2 ≤ 4) : matchedA e ≠ 0 := by
  intro h; have := matchedA_norm he; rw [h, norm_zero] at this; norm_num at this

/-- `a⁻¹ = -e - a`, i.e. `a + a⁻¹ = -e`. -/
theorem matchedA_inv {e : ℝ} (he : e ^ 2 ≤ 4) : (matchedA e)⁻¹ = -(e : ℂ) - matchedA e := by
  refine inv_eq_of_mul_eq_one_right ?_
  have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 4 - e ^ 2)
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re,
      Complex.sub_im, Complex.neg_im, Complex.ofReal_im, matchedA_re, matchedA_im, Complex.one_re]
    nlinarith
  · simp only [Complex.mul_im, Complex.sub_re, Complex.neg_re, Complex.ofReal_re,
      Complex.sub_im, Complex.neg_im, Complex.ofReal_im, matchedA_re, matchedA_im, Complex.one_im]
    ring

theorem boundaryZ_eq {b e : ℝ} (he : e ^ 2 ≤ 4) :
    boundaryZ b e = -(e : ℂ) - matchedA e + b * matchedA e := by
  unfold boundaryZ; rw [matchedA_inv he]

theorem boundaryZ_im {b e : ℝ} (he : e ^ 2 ≤ 4) :
    (boundaryZ b e).im = (1 - b) * (Real.sqrt (4 - e ^ 2) / 2) := by
  rw [boundaryZ_eq he]; simp [matchedA_im]; ring

theorem boundaryZ_norm_le {b e : ℝ} (hb : 0 ≤ b) (he : e ^ 2 ≤ 4) : ‖boundaryZ b e‖ ≤ 1 + b := by
  unfold boundaryZ
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_inv, norm_mul, matchedA_norm he, Complex.norm_real, Real.norm_of_nonneg hb]; simp

/-!
## The chain in matrix form
-/

/-- The chain values at zero-based positions: `M_k = m_{k+1}`. -/
def chainM (m : ℕ → ℂ) (J : ℕ) (k : Fin (J + 1)) : ℂ := m (k + 1)

/-- `S` as a function on `Fin (J+1)`. -/
def chainSf (b : ℝ) (J : ℕ) (k l : Fin (J + 1)) : ℝ := chainS b J k l

/-- The diagonal vector `d = (-e, …, -e, z)`. -/
def chainD (b e : ℝ) (J : ℕ) (k : Fin (J + 1)) : ℂ :=
  if (k : ℕ) < J then -(e : ℂ) else boundaryZ b e

section Chain

variable {b e : ℝ} {J : ℕ} {m : ℕ → ℂ}

/-- the finite Dyson equation in matrix form: `M_k⁻¹ = d_k - (S M)_k`. -/
theorem chain_matrix_eq (h : IsZeroEntranceChain b e J m) (k : Fin (J + 1)) :
    (chainM m J k)⁻¹ = chainD b e J k - cmv (chainSf b J) (chainM m J) k := by
  have hs := sum_chainS (J := J) b m h.zero k
  unfold cmv chainSf chainM
  rw [hs]
  unfold chainD
  by_cases hk : (k : ℕ) < J
  · simp only [hk, ↓reduceIte]
    rw [h.bulk (k + 1) (by omega) (by omega)]
    simp only [Nat.add_sub_cancel, show (k : ℕ) + 1 + 1 = k + 2 by omega]
    ring
  · have hkJ : (k : ℕ) = J := by have := k.2; omega
    simp only [hk, ↓reduceIte]
    rw [hkJ, h.port]
    ring

theorem chainM_im_neg (h : IsZeroEntranceChain b e J m) (k : Fin (J + 1)) :
    (chainM m J k).im < 0 := h.im_neg (k + 1) (by omega) (by have := k.2; omega)

/-- Row sums of `S`. -/
theorem chainSf_rowsum (b : ℝ) (k : Fin (J + 1)) :
    ∑ l, chainSf b J k l =
      (if (k : ℕ) < J then (1 - 2 * b) + b else 0) + (if 1 ≤ (k : ℕ) then b else 0) := by
  have hs := sum_chainS (J := J) b (fun n => if n = 0 then 0 else 1) (by simp) k
  have hre := congrArg Complex.re hs
  unfold chainSf
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hre
  have h1 : ∀ x : Fin (J + 1), ((if (x : ℕ) + 1 = 0 then (0 : ℂ) else 1)).re = 1 := fun x => by
    simp
  simp only [h1, mul_one] at hre
  rw [hre]
  rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | h0
  · rw [h0]; by_cases hJ : 0 < J <;> simp [hJ]
  · by_cases hk : (k : ℕ) < J <;>
      simp [hk, show 1 ≤ (k : ℕ) by omega, show (k : ℕ) ≠ 0 by omega]

end Chain

/-!
## Imaginary parts and Step 4
-/

section Bounds

variable {b e : ℝ} {J : ℕ} {m : ℕ → ℂ}

/-- `y_k = -Im M_k`. -/
def chainY (m : ℕ → ℂ) (J : ℕ) (k : Fin (J + 1)) : ℝ := -(chainM m J k).im

theorem chainD_im_nonneg (hb : b ≤ 1) (he : e ^ 2 ≤ 4) (k : Fin (J + 1)) :
    0 ≤ (chainD b e J k).im := by
  unfold chainD
  split_ifs
  · simp
  · rw [boundaryZ_im he]
    have := Real.sqrt_nonneg (4 - e ^ 2)
    nlinarith

theorem chainY_pos (h : IsZeroEntranceChain b e J m) (k : Fin (J + 1)) : 0 < chainY m J k := by
  unfold chainY; linarith [chainM_im_neg h k]

theorem chainM_ne_zero (h : IsZeroEntranceChain b e J m) (k : Fin (J + 1)) :
    chainM m J k ≠ 0 := fun h0 => by have := chainM_im_neg h k; rw [h0] at this; simp at this

/-- The imaginary identity `y_k / |M_k|² = Im d_k + (S y)_k`. -/
theorem chain_im_identity (h : IsZeroEntranceChain b e J m) (k : Fin (J + 1)) :
    chainY m J k / ‖chainM m J k‖ ^ 2 = (chainD b e J k).im + mv (chainSf b J) (chainY m J) k := by
  have hE := congrArg Complex.im (chain_matrix_eq h k)
  rw [Complex.inv_im, Complex.sub_im, cmv_im] at hE
  have hmv : mv (chainSf b J) (chainY m J) k = -mv (chainSf b J) (fun j => (chainM m J j).im) k := by
    unfold mv chainY; rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hmv, Complex.sq_norm]
  unfold chainY
  rw [neg_div, ← neg_div, hE]; ring

theorem chain_Sy_le (h : IsZeroEntranceChain b e J m) (hb : b ≤ 1) (he : e ^ 2 ≤ 4)
    (k : Fin (J + 1)) :
    mv (chainSf b J) (chainY m J) k ≤ chainY m J k / ‖chainM m J k‖ ^ 2 := by
  rw [chain_im_identity h k]; linarith [chainD_im_nonneg (J := J) hb he k]

theorem chainSf_nonneg (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b) (k l : Fin (J + 1)) :
    0 ≤ chainSf b J k l := chainS_nonneg hb hc _ _ _

theorem chainSf_symm (k l : Fin (J + 1)) : chainSf b J k l = chainSf b J l k := chainS_symm _ _ _ _

theorem chainSf_rowsum_le (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b) (k : Fin (J + 1)) :
    ∑ l, chainSf b J k l ≤ 1 := by
  rw [chainSf_rowsum]
  split_ifs <;> linarith

theorem chainSf_rowsum_port (hb : 0 ≤ b) (k : Fin (J + 1)) (hk : ¬ (k : ℕ) < J) :
    ∑ l, chainSf b J k l ≤ b := by
  rw [chainSf_rowsum]
  simp only [hk, ↓reduceIte, zero_add]
  split_ifs <;> linarith

/-- **Step 4**, upper bounds: `c |M_k|² ≤ 1` on the physical sites and
`|M_J| Im z ≤ 1` at the port. -/
theorem chain_upper (h : IsZeroEntranceChain b e J m) (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b)
    (k : Fin (J + 1)) :
    ((k : ℕ) < J → (1 - 2 * b) * ‖chainM m J k‖ ^ 2 ≤ 1) ∧
      (¬ (k : ℕ) < J → ‖chainM m J k‖ * (boundaryZ b e).im ≤ 1) := by
  have hy := chainY_pos h k
  have hM := norm_pos_iff.mpr (chainM_ne_zero h k)
  have hId := chain_im_identity h k
  have hSy0 : 0 ≤ mv (chainSf b J) (chainY m J) k :=
    Finset.sum_nonneg fun l _ => mul_nonneg (chainSf_nonneg hb hc k l) (chainY_pos h l).le
  constructor
  · intro hk
    have hsingle : chainSf b J k k * chainY m J k ≤ mv (chainSf b J) (chainY m J) k :=
      Finset.single_le_sum (f := fun l => chainSf b J k l * chainY m J l)
        (fun l _ => mul_nonneg (chainSf_nonneg hb hc k l) (chainY_pos h l).le) (Finset.mem_univ k)
    have hd : chainSf b J k k = 1 - 2 * b := by unfold chainSf; rw [chainS_diag]; simp [hk]
    rw [hd] at hsingle
    have hD : (chainD b e J k).im = 0 := by unfold chainD; simp [hk]
    rw [hD, zero_add] at hId
    have : (1 - 2 * b) * chainY m J k ≤ chainY m J k / ‖chainM m J k‖ ^ 2 := by linarith
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  · intro hk
    have hD : (chainD b e J k).im = (boundaryZ b e).im := by unfold chainD; simp [hk]
    rw [hD] at hId
    have hyM : chainY m J k ≤ ‖chainM m J k‖ := by
      unfold chainY
      have := Complex.abs_im_le_norm (chainM m J k); rw [abs_le] at this; linarith
    have h1 : (boundaryZ b e).im ≤ chainY m J k / ‖chainM m J k‖ ^ 2 := by linarith
    have h2 : chainY m J k / ‖chainM m J k‖ ^ 2 ≤ 1 / ‖chainM m J k‖ := by
      rw [div_le_div_iff₀ (by positivity) hM]; nlinarith
    have := h1.trans h2
    rw [le_div_iff₀ hM] at this
    linarith

/-- **Step 4**: `r ≤ |M_k| ≤ R` for every `R` with `c R² ≥ 1`,
`R Im z ≥ 1`, and `r = 1/(2 + R)`. -/
theorem chain_bounds (h : IsZeroEntranceChain b e J m) (hb : 0 ≤ b) (hc : 0 < 1 - 2 * b)
    (he : e ^ 2 ≤ 4) {R : ℝ} (hR0 : 0 ≤ R) (hR1 : 1 ≤ (1 - 2 * b) * R ^ 2)
    (hR2 : 1 ≤ R * (boundaryZ b e).im) (k : Fin (J + 1)) :
    1 / (2 + R) ≤ ‖chainM m J k‖ ∧ ‖chainM m J k‖ ≤ R := by
  have hup : ∀ l : Fin (J + 1), ‖chainM m J l‖ ≤ R := by
    intro l
    obtain ⟨h1, h2⟩ := chain_upper h hb hc.le l
    by_cases hl : (l : ℕ) < J
    · have := h1 hl
      nlinarith [norm_nonneg (chainM m J l)]
    · have := h2 hl
      have hz : 0 < (boundaryZ b e).im := by
        by_contra hz; push Not at hz; nlinarith
      by_contra hc'
      push Not at hc'
      nlinarith
  refine ⟨?_, hup k⟩
  have hM := norm_pos_iff.mpr (chainM_ne_zero h k)
  have hinv : ‖(chainM m J k)⁻¹‖ ≤ 2 + R := by
    rw [chain_matrix_eq h k]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · unfold chainD
      split_ifs
      · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
        have : |e| ≤ 2 := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (e + 2), sq_nonneg (e - 2)]
        exact this
      · have := boundaryZ_norm_le hb he; linarith
    · unfold cmv
      refine (norm_sum_le _ _).trans ?_
      calc ∑ l, ‖(chainSf b J k l : ℂ) * chainM m J l‖ ≤ ∑ l, chainSf b J k l * R := by
            refine Finset.sum_le_sum fun l _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (chainSf_nonneg hb hc.le k l)]
            exact mul_le_mul_of_nonneg_left (hup l) (chainSf_nonneg hb hc.le k l)
        _ = (∑ l, chainSf b J k l) * R := by rw [Finset.sum_mul]
        _ ≤ 1 * R := mul_le_mul_of_nonneg_right (chainSf_rowsum_le hb hc.le k) hR0
        _ = R := one_mul R
  rw [norm_inv] at hinv
  rw [div_le_iff₀ (by linarith)]
  have := (inv_le_iff_one_le_mul₀ hM).mp hinv
  linarith

end Bounds

/-!
## Step 5: the symmetrized matrix
-/

section Spectrum

variable {b e : ℝ} {J : ℕ} {m : ℕ → ℂ}

/-- The symmetrized matrix `A = R_m S R_m`, `R_m = diag(√|m_ℓ|)`. -/
def chainA (b : ℝ) (m : ℕ → ℂ) (J : ℕ) (k l : Fin (J + 1)) : ℝ :=
  Real.sqrt ‖chainM m J k‖ * chainSf b J k l * Real.sqrt ‖chainM m J l‖

/-- The subinvariant vector `φ = R_m⁻¹ √y` (with a constant factor `√y_a`
dropped). -/
def chainPhi (m : ℕ → ℂ) (J : ℕ) (k : Fin (J + 1)) : ℝ :=
  Real.sqrt (chainY m J k) / Real.sqrt ‖chainM m J k‖

theorem chainA_symm (k l : Fin (J + 1)) : chainA b m J k l = chainA b m J l k := by
  unfold chainA; rw [chainSf_symm]; ring

theorem chainA_nonneg (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b) (k l : Fin (J + 1)) :
    0 ≤ chainA b m J k l := by
  unfold chainA; have := chainSf_nonneg (J := J) hb hc k l; positivity

theorem chainPhi_pos (h : IsZeroEntranceChain b e J m) (k : Fin (J + 1)) :
    0 < chainPhi m J k := by
  unfold chainPhi
  have := Real.sqrt_pos.mpr (chainY_pos h k)
  have := Real.sqrt_pos.mpr (norm_pos_iff.mpr (chainM_ne_zero h k))
  positivity

/-- Subinvariance `(Aφ)_k ≤ √(Σ_l S_kl) φ_k`. -/
theorem chain_subinvariant (h : IsZeroEntranceChain b e J m) (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b)
    (he : e ^ 2 ≤ 4) (k : Fin (J + 1)) :
    mv (chainA b m J) (chainPhi m J) k ≤ Real.sqrt (∑ l, chainSf b J k l) * chainPhi m J k := by
  have hM : ∀ l : Fin (J + 1), 0 < ‖chainM m J l‖ := fun l => norm_pos_iff.mpr (chainM_ne_zero h l)
  have hy : ∀ l : Fin (J + 1), 0 < chainY m J l := chainY_pos h
  have hS := chainSf_nonneg (J := J) hb hc
  have heq : mv (chainA b m J) (chainPhi m J) k =
      Real.sqrt ‖chainM m J k‖ * ∑ l, chainSf b J k l * Real.sqrt (chainY m J l) := by
    unfold mv chainA chainPhi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := Real.sqrt_pos.mpr (hM l)
    field_simp
  have hcs := CavityMean.weighted_cs (chainSf b J k) (fun l => Real.sqrt (chainY m J l))
    (fun _ => 1) (hS k)
  simp only [mul_one, one_pow, Real.sq_sqrt (hy _).le] at hcs
  have hSy := chain_Sy_le h (by linarith) he k
  have hT0 : 0 ≤ ∑ l, chainSf b J k l * Real.sqrt (chainY m J l) :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hS k l) (Real.sqrt_nonneg _)
  have hrs0 : 0 ≤ ∑ l, chainSf b J k l := Finset.sum_nonneg fun l _ => hS k l
  have hlhs0 : 0 ≤ mv (chainA b m J) (chainPhi m J) k := by
    rw [heq]; positivity
  have hrhs0 : 0 ≤ Real.sqrt (∑ l, chainSf b J k l) * chainPhi m J k :=
    mul_nonneg (Real.sqrt_nonneg _) (chainPhi_pos h k).le
  refine (pow_le_pow_iff_left₀ hlhs0 hrhs0 two_ne_zero).mp ?_
  rw [heq, mul_pow, mul_pow, Real.sq_sqrt (hM k).le, Real.sq_sqrt hrs0]
  unfold chainPhi
  rw [div_pow, Real.sq_sqrt (hy k).le, Real.sq_sqrt (hM k).le]
  calc ‖chainM m J k‖ * (∑ l, chainSf b J k l * Real.sqrt (chainY m J l)) ^ 2
      ≤ ‖chainM m J k‖ * (mv (chainSf b J) (chainY m J) k * ∑ l, chainSf b J k l) :=
        mul_le_mul_of_nonneg_left hcs (hM k).le
    _ ≤ ‖chainM m J k‖ * (chainY m J k / ‖chainM m J k‖ ^ 2 * ∑ l, chainSf b J k l) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSy hrs0) (hM k).le
    _ = (∑ l, chainSf b J k l) * (chainY m J k / ‖chainM m J k‖) := by
        have := (hM k).ne'; field_simp

/-- **Step 5**: `Spec A ⊂ [-1 + δ_*, 1]` in quadratic-form sense, with
`δ_* = min(2 c r, 1 - √b)` whenever `r ≤ |m_ℓ|` for all sites. -/
theorem chain_spectrum (h : IsZeroEntranceChain b e J m) (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b)
    (he : e ^ 2 ≤ 4) {r : ℝ} (hr : ∀ k : Fin (J + 1), r ≤ ‖chainM m J k‖) :
    (∀ x : Fin (J + 1) → ℝ, bf (chainA b m J) x x ≤ nsq x) ∧
      (∀ x : Fin (J + 1) → ℝ,
        min (2 * (1 - 2 * b) * r) (1 - Real.sqrt b) * nsq x ≤ nsq x + bf (chainA b m J) x x) := by
  set ρ : Fin (J + 1) → ℝ := fun k => Real.sqrt (∑ l, chainSf b J k l)
  have hsub : ∀ k, mv (chainA b m J) (chainPhi m J) k ≤ ρ k * chainPhi m J k :=
    chain_subinvariant h hb hc he
  have hρ1 : ∀ k, ρ k ≤ 1 := fun k => by
    simp only [ρ]; rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (chainSf_rowsum_le hb hc k)
  have hsym : ∀ k l, chainA b m J k l = chainA b m J l k := chainA_symm
  have hA := chainA_nonneg (m := m) (J := J) hb hc
  have hφ := chainPhi_pos h
  constructor
  · intro x
    refine (qf_le_of_subinvariant hsym hA hφ hsub x).trans ?_
    unfold nsq
    exact Finset.sum_le_sum fun i _ => by
      nlinarith [hρ1 i, sq_nonneg (x i)]
  · intro x
    have hge := qf_ge_of_subinvariant hsym hA hφ hsub x
    have hpt : ∀ i, min (2 * (1 - 2 * b) * r) (1 - Real.sqrt b) ≤ 1 + (2 * chainA b m J i i - ρ i) := by
      intro i
      by_cases hi : (i : ℕ) < J
      · have hd : chainA b m J i i = ‖chainM m J i‖ * (1 - 2 * b) := by
          unfold chainA chainSf
          rw [chainS_diag]; simp only [hi, ↓reduceIte]
          have := Real.mul_self_sqrt (norm_nonneg (chainM m J i))
          nlinarith
        have : 2 * (1 - 2 * b) * r ≤ 2 * chainA b m J i i := by
          rw [hd]; nlinarith [hr i]
        have := min_le_left (2 * (1 - 2 * b) * r) (1 - Real.sqrt b)
        linarith [hρ1 i]
      · have hd : chainA b m J i i = 0 := by
          unfold chainA chainSf; rw [chainS_diag]; simp [hi]
        have hρb : ρ i ≤ Real.sqrt b := Real.sqrt_le_sqrt (chainSf_rowsum_port hb i hi)
        have := min_le_right (2 * (1 - 2 * b) * r) (1 - Real.sqrt b)
        rw [hd]; linarith
    have : min (2 * (1 - 2 * b) * r) (1 - Real.sqrt b) * nsq x ≤
        ∑ i, (1 + (2 * chainA b m J i i - ρ i)) * x i ^ 2 := by
      unfold nsq; rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hpt i) (sq_nonneg _)
    have hsplit : ∑ i, (1 + (2 * chainA b m J i i - ρ i)) * x i ^ 2 =
        nsq x + ∑ i, (2 * chainA b m J i i - ρ i) * x i ^ 2 := by
      unfold nsq; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    linarith

/-- The Schur norm bound `‖A|x|‖ ≤ ‖x‖` for the chain matrix. -/
theorem chain_schur (h : IsZeroEntranceChain b e J m) (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b)
    (he : e ^ 2 ≤ 4) (x : Fin (J + 1) → ℝ) :
    ∑ i, (∑ j, chainA b m J i j * |x j|) ^ 2 ≤ ∑ j, x j ^ 2 := by
  refine schur_norm_le chainA_symm (chainA_nonneg hb hc) (chainPhi_pos h) (fun k => ?_) x
  refine (chain_subinvariant h hb hc he k).trans ?_
  have : Real.sqrt (∑ l, chainSf b J k l) ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (chainSf_rowsum_le hb hc k)
  nlinarith [chainPhi_pos h k]

theorem chainA_tri (k l : Fin (J + 1)) (h : chainA b m J k l ≠ 0) :
    (k : ℕ) ≤ l + 1 ∧ (l : ℕ) ≤ k + 1 := by
  apply chainS_tri (b := b) (J := J)
  intro h0
  apply h
  unfold chainA chainSf
  rw [h0]; ring

end Spectrum

/-!
## Steps 6–7: the phase, the difference equation and the seed
-/

section Seed

variable {b e : ℝ} {J : ℕ} {m : ℕ → ℂ}

/-- The diagonal unitary `Θ = diag(a m_ℓ / |m_ℓ|)`. -/
def chainTheta (e : ℝ) (m : ℕ → ℂ) (J : ℕ) (k : Fin (J + 1)) : ℂ :=
  matchedA e * chainM m J k / (‖chainM m J k‖ : ℂ)

theorem chainTheta_norm (h : IsZeroEntranceChain b e J m) (he : e ^ 2 ≤ 4) (k : Fin (J + 1)) :
    ‖chainTheta e m J k‖ = 1 := by
  have hM := norm_pos_iff.mpr (chainM_ne_zero h k)
  unfold chainTheta
  rw [norm_div, norm_mul, matchedA_norm he, Complex.norm_real, Real.norm_of_nonneg hM.le]
  field_simp

/-- `|1 - Θ_k| ≥ √(4 - e²)/2`. -/
theorem chainTheta_gap (h : IsZeroEntranceChain b e J m) (he : e ^ 2 ≤ 4) (k : Fin (J + 1)) :
    Real.sqrt (4 - e ^ 2) / 2 ≤ ‖1 - chainTheta e m J k‖ := by
  have hM := norm_pos_iff.mpr (chainM_ne_zero h k)
  set w : ℂ := chainM m J k / (‖chainM m J k‖ : ℂ)
  have hw : w.im ≤ 0 := by
    simp only [w, Complex.div_ofReal_im]
    exact div_nonpos_of_nonpos_of_nonneg (chainM_im_neg h k).le hM.le
  have ha := matchedA_ne_zero he
  have heq : 1 - chainTheta e m J k = matchedA e * ((matchedA e)⁻¹ - w) := by
    unfold chainTheta; simp only [w]; rw [mul_sub, mul_inv_cancel₀ ha]; ring
  rw [heq, norm_mul, matchedA_norm he, one_mul]
  refine le_trans ?_ (Complex.im_le_norm _)
  rw [Complex.sub_im, matchedA_inv he]
  simp [matchedA_im]
  linarith

/-- The reference identity: `a⁻¹ = d_k - b a [k = 0] - a (Σ_l S_kl)`. -/
theorem chain_reference (he : e ^ 2 ≤ 4) (k : Fin (J + 1)) :
    (matchedA e)⁻¹ = chainD b e J k - (if (k : ℕ) = 0 then (b : ℂ) * matchedA e else 0) -
      matchedA e * ((∑ l, chainSf b J k l : ℝ) : ℂ) := by
  rw [chainSf_rowsum, matchedA_inv he]
  unfold chainD
  have hz := boundaryZ_eq (b := b) he
  by_cases hk : (k : ℕ) < J
  · rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | h0
    · rw [h0] at hk ⊢
      simp only [hk, ↓reduceIte, show ¬ (1 ≤ 0) by omega]; push_cast; ring
    · simp only [hk, ↓reduceIte, show (k : ℕ) ≠ 0 by omega, show 1 ≤ (k : ℕ) by omega]
      push_cast; ring
  · rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | h0
    · rw [h0] at hk ⊢
      simp only [hk, ↓reduceIte, show ¬ (1 ≤ 0) by omega]; rw [hz]; push_cast; ring
    · simp only [hk, ↓reduceIte, show (k : ℕ) ≠ 0 by omega, show 1 ≤ (k : ℕ) by omega]
      rw [hz]; push_cast; ring

/-- The rescaled difference `x_k = (m_{k+1} - a)/√|m_{k+1}|`. -/
def chainX (e : ℝ) (m : ℕ → ℂ) (J : ℕ) (k : Fin (J + 1)) : ℂ :=
  (chainM m J k - matchedA e) / (Real.sqrt ‖chainM m J k‖ : ℂ)

/-- **Step 7**: `(I - ΘA) x = -b a² √|m₁| (m₁/|m₁|) e₁`, i.e. the difference
`Δ = m - a1` solves `(I - diag(a m)S)Δ = -b m₁ a² e₁` after the similarity by `R_m`. -/
theorem chain_difference_eq (h : IsZeroEntranceChain b e J m) (he : e ^ 2 ≤ 4)
    (k : Fin (J + 1)) :
    chainX e m J k - chainTheta e m J k * cmv (chainA b m J) (chainX e m J) k =
      if (k : ℕ) = 0 then -(b : ℂ) * matchedA e ^ 2 * chainM m J k /
        (Real.sqrt ‖chainM m J k‖ : ℂ) else 0 := by
  have hM := norm_pos_iff.mpr (chainM_ne_zero h k)
  have hMne := chainM_ne_zero h k
  have hsq := Real.sqrt_pos.mpr hM
  have ha := matchedA_ne_zero he
  set s : ℝ := Real.sqrt ‖chainM m J k‖ with hs
  have hs2 : (s : ℂ) * s = (‖chainM m J k‖ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (norm_nonneg _)]
  have hsne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq.ne'
  have hnne : (‖chainM m J k‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM.ne'
  -- `(A x)_k = √|M_k| ((S M)_k - a Σ_l S_kl)`
  have hAx : cmv (chainA b m J) (chainX e m J) k =
      (s : ℂ) * (cmv (chainSf b J) (chainM m J) k -
        matchedA e * ((∑ l, chainSf b J k l : ℝ) : ℂ)) := by
    unfold cmv chainA chainX
    push_cast
    rw [Finset.mul_sum, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hl := Real.sqrt_pos.mpr (norm_pos_iff.mpr (chainM_ne_zero h l))
    have hlne : ((Real.sqrt ‖chainM m J l‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl.ne'
    field_simp
    ring
  have hE := chain_matrix_eq h k
  have hR := chain_reference (J := J) (b := b) he k
  rw [hAx]
  unfold chainX chainTheta
  rw [← hs]
  -- eliminate `(S M)_k` and `a Σ S`
  have hSM : cmv (chainSf b J) (chainM m J) k = chainD b e J k - (chainM m J k)⁻¹ := by
    rw [hE]; ring
  have hAS : matchedA e * ((∑ l, chainSf b J k l : ℝ) : ℂ) = chainD b e J k -
      (if (k : ℕ) = 0 then (b : ℂ) * matchedA e else 0) - (matchedA e)⁻¹ := by
    rw [hR]; ring
  rw [hSM, hAS]
  split_ifs with hk0
  · field_simp
    rw [← hs2]
    field_simp
    ring
  · field_simp
    rw [← hs2]
    field_simp
    ring

end Seed

/-!
## Uniform constants on the compact parameter set `κ ≤ b`, `κ ≤ 1 - 2b`, `κ ≤ 4 - e²`
-/

/-- `R_κ = 4/√κ`, the upper bound of Step 4. -/
def seedR (κ : ℝ) : ℝ := 4 / Real.sqrt κ
/-- `r_κ = 1/(2 + R_κ)`, the lower bound of Step 4. -/
def seedr (κ : ℝ) : ℝ := 1 / (2 + seedR κ)
/-- `δ_κ = min(2 κ r_κ, 1/4)`, the spectral gap of Step 5. -/
def seedDelta (κ : ℝ) : ℝ := min (2 * κ * seedr κ) (1 / 4)
/-- `κ₀ = min(δ/2, δ² δ_κ/16)` with `δ = √κ/2`, the singular-value bound of Step 6. -/
def seedKappa (κ : ℝ) : ℝ :=
  min (Real.sqrt κ / 2 / 2) ((Real.sqrt κ / 2) ^ 2 * seedDelta κ / 16)
/-- The decay rate `c_* = log(1 + κ₀/2)`. -/
def seedRate (κ : ℝ) : ℝ := Real.log (1 + seedKappa κ / 2)
/-- The seed constant `C = R_κ/κ₀`. -/
def seedConst (κ : ℝ) : ℝ := seedR κ / seedKappa κ

theorem seed_consts_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < seedR κ ∧ 0 < seedr κ ∧ 0 < seedDelta κ ∧ 0 < seedKappa κ ∧ 0 < seedRate κ ∧
      0 < seedConst κ := by
  have hs := Real.sqrt_pos.mpr hκ
  have hR : 0 < seedR κ := by unfold seedR; positivity
  have hr : 0 < seedr κ := by unfold seedr; positivity
  have hd : 0 < seedDelta κ := lt_min (by positivity) (by norm_num)
  have hk : 0 < seedKappa κ := lt_min (by positivity) (by positivity)
  have ht : 0 < seedRate κ := Real.log_pos (by linarith)
  exact ⟨hR, hr, hd, hk, ht, by unfold seedConst; positivity⟩

section Params

variable {κ b e : ℝ}

theorem params_facts (hκ : 0 < κ) (hb : κ ≤ b) (hc : κ ≤ 1 - 2 * b) (he : κ ≤ 4 - e ^ 2) :
    0 < b ∧ 0 < 1 - 2 * b ∧ e ^ 2 ≤ 4 ∧ 1 ≤ (1 - 2 * b) * seedR κ ^ 2 ∧
      1 ≤ seedR κ * (boundaryZ b e).im ∧ Real.sqrt κ / 2 ≤ Real.sqrt (4 - e ^ 2) / 2 := by
  have hs := Real.sqrt_pos.mpr hκ
  have hss := Real.sq_sqrt hκ.le
  have he4 : e ^ 2 ≤ 4 := by linarith
  have hsq : Real.sqrt κ ≤ Real.sqrt (4 - e ^ 2) := Real.sqrt_le_sqrt he
  refine ⟨by linarith, by linarith, he4, ?_, ?_, by linarith⟩
  · unfold seedR
    rw [div_pow, hss, mul_div_assoc', le_div_iff₀ hκ]
    nlinarith
  · rw [boundaryZ_im he4]
    unfold seedR
    rw [div_mul_eq_mul_div, le_div_iff₀ hs]
    nlinarith

end Params

end ZeroEntrance

open ZeroEntrance

/-!
## Main statements
-/

/-- **Step 4** of the zero-entrance lemma: uniformly in `J` and in the compact
parameter set, `r_κ ≤ |m_ℓ| ≤ R_κ` for `1 ≤ ℓ ≤ J+1`. -/
theorem zeroEntrance_bounds {κ : ℝ} (hκ : 0 < κ) {b e : ℝ} (hb : κ ≤ b) (hc : κ ≤ 1 - 2 * b)
    (he : κ ≤ 4 - e ^ 2) {J : ℕ} {m : ℕ → ℂ} (h : IsZeroEntranceChain b e J m) (ℓ : ℕ)
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ J + 1) :
    seedr κ ≤ ‖m ℓ‖ ∧ ‖m ℓ‖ ≤ seedR κ := by
  obtain ⟨hb0, hc0, he4, hR1, hR2, -⟩ := params_facts hκ hb hc he
  have := chain_bounds h hb0.le hc0 he4 (seed_consts_pos hκ).1.le hR1 hR2 ⟨ℓ - 1, by omega⟩
  unfold chainM at this
  simp only [show ℓ - 1 + 1 = ℓ by omega] at this
  exact this

/-- **Step 5** of the zero-entrance lemma: the symmetrized matrix
`A = R_m S R_m` satisfies `xᵀAx ≤ |x|²` and `|x|² + xᵀAx ≥ δ_κ |x|²` for every real `x`
(`Spec A ⊂ [-1 + δ_κ, 1]`), uniformly in `J` and in the compact parameter set. -/
theorem zeroEntrance_spectrum {κ : ℝ} (hκ : 0 < κ) {b e : ℝ} (hb : κ ≤ b) (hc : κ ≤ 1 - 2 * b)
    (he : κ ≤ 4 - e ^ 2) {J : ℕ} {m : ℕ → ℂ} (h : IsZeroEntranceChain b e J m) :
    (∀ x : Fin (J + 1) → ℝ, bf (chainA b m J) x x ≤ nsq x) ∧
      (∀ x : Fin (J + 1) → ℝ, seedDelta κ * nsq x ≤ nsq x + bf (chainA b m J) x x) := by
  obtain ⟨hb0, hc0, he4, hR1, hR2, -⟩ := params_facts hκ hb hc he
  have hr : ∀ k : Fin (J + 1), seedr κ ≤ ‖chainM m J k‖ := fun k =>
    (chain_bounds h hb0.le hc0 he4 (seed_consts_pos hκ).1.le hR1 hR2 k).1
  obtain ⟨hup, hlow⟩ := chain_spectrum h hb0.le hc0.le he4 hr
  refine ⟨hup, fun x => le_trans ?_ (hlow x)⟩
  refine mul_le_mul_of_nonneg_right ?_ (nsq_nonneg x)
  have hr0 := (seed_consts_pos hκ).2.1
  have h1 : 2 * κ * seedr κ ≤ 2 * (1 - 2 * b) * seedr κ := by nlinarith
  have h2 : (1 : ℝ) / 4 ≤ 1 - Real.sqrt b := by
    have : Real.sqrt b ≤ 3 / 4 := by
      rw [show (3 : ℝ) / 4 = Real.sqrt ((3 / 4) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  unfold seedDelta
  exact min_le_min h1 h2

/-- **Step 6** of the zero-entrance lemma: the uniform lower bound
`|(I - ΘA)x| ≥ κ₀ |x|` on the smallest singular value, `Θ = diag(a m_ℓ/|m_ℓ|)`. -/
theorem zeroEntrance_singular_lower {κ : ℝ} (hκ : 0 < κ) {b e : ℝ} (hb : κ ≤ b)
    (hc : κ ≤ 1 - 2 * b) (he : κ ≤ 4 - e ^ 2) {J : ℕ} {m : ℕ → ℂ}
    (h : IsZeroEntranceChain b e J m) (x : Fin (J + 1) → ℂ) :
    seedKappa κ * cnorm x ≤
      cnorm (fun k => x k - chainTheta e m J k * cmv (chainA b m J) x k) := by
  obtain ⟨-, -, he4, -, -, hδ⟩ := params_facts hκ hb hc he
  obtain ⟨hup, hlow⟩ := zeroEntrance_spectrum hκ hb hc he h
  have hs := Real.sqrt_pos.mpr hκ
  exact lower_bound_ThetaA chainA_symm (seed_consts_pos hκ).2.2.1 (by positivity) hup hlow
    (chainTheta_norm h he4) (fun k => hδ.trans (chainTheta_gap h he4 k)) x

/-- **The finite seed bound**: for the finite chain of the finite Dyson equation with zero boundary, `|m_{J+1} - a| ≤ C e^{-c_* J}`,
with `C = seedConst κ`, `c_* = seedRate κ` uniform in `J` and in the compact parameter set
`κ ≤ b`, `κ ≤ 1 - 2b`, `κ ≤ 4 - e²`. The argument does not assume `z⁻¹` close to `a`. -/
theorem zeroEntrance_finite_seed {κ : ℝ} (hκ : 0 < κ) {b e : ℝ} (hb : κ ≤ b)
    (hc : κ ≤ 1 - 2 * b) (he : κ ≤ 4 - e ^ 2) {J : ℕ} {m : ℕ → ℂ}
    (h : IsZeroEntranceChain b e J m) :
    ‖m (J + 1) - matchedA e‖ ≤ seedConst κ * Real.exp (-seedRate κ * J) := by
  obtain ⟨hb0, hc0, he4, hR1, hR2, -⟩ := params_facts hκ hb hc he
  obtain ⟨hR, -, -, hk, ht, -⟩ := seed_consts_pos hκ
  have hbd : ∀ k : Fin (J + 1), seedr κ ≤ ‖chainM m J k‖ ∧ ‖chainM m J k‖ ≤ seedR κ := fun k =>
    chain_bounds h hb0.le hc0 he4 hR.le hR1 hR2 k
  set t := seedRate κ with htdef
  set κ₀ := seedKappa κ
  set E : Fin (J + 1) → ℝ := fun k => Real.exp (t * (k : ℕ))
  set x := chainX e m J
  set w : Fin (J + 1) → ℂ := fun k => (E k : ℂ) * x k
  have het : Real.exp t - 1 = κ₀ / 2 := by
    rw [htdef]; unfold seedRate; rw [Real.exp_log (by positivity)]; ring
  have hdec := decay_commutator (chainA_nonneg (m := m) (J := J) hb0.le hc0.le)
    (fun k => (k : ℕ)) (fun k l hkl => chainA_tri k l hkl)
    (chain_schur h hb0.le hc0.le he4) (chainTheta_norm h he4) ht.le x
  have hlow := zeroEntrance_singular_lower hκ hb hc he h w
  rw [het] at hdec
  -- the source term
  set src : Fin (J + 1) → ℂ := fun k => (E k : ℂ) * (x k - chainTheta e m J k *
    cmv (chainA b m J) x k)
  have hsrc : cnorm src ≤ b * Real.sqrt (seedR κ) := by
    have hpt : ∀ k : Fin (J + 1), ‖src k‖ ^ 2 ≤
        if (k : ℕ) = 0 then (b * Real.sqrt (seedR κ)) ^ 2 else 0 := by
      intro k
      simp only [src, x]
      rw [chain_difference_eq h he4 k]
      split_ifs with hk0
      · have hM := norm_pos_iff.mpr (chainM_ne_zero h k)
        have hsq := Real.sqrt_pos.mpr hM
        have hE0 : E k = 1 := by simp [E, hk0]
        rw [hE0]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        rw [Complex.ofReal_one, one_mul, norm_div, norm_mul, norm_mul, norm_neg, norm_pow,
          matchedA_norm he4, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hb0.le,
          Real.norm_of_nonneg hsq.le, one_pow, mul_one]
        have : ‖chainM m J k‖ / Real.sqrt ‖chainM m J k‖ = Real.sqrt ‖chainM m J k‖ :=
          Real.div_sqrt
        rw [mul_div_assoc, this]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hbd k).2) hb0.le
      · simp
    unfold cnorm cnsq
    rw [← Real.sqrt_sq (by have := Real.sqrt_nonneg (seedR κ); positivity :
      0 ≤ b * Real.sqrt (seedR κ))]
    refine Real.sqrt_le_sqrt ((Finset.sum_le_sum fun k _ => hpt k).trans (le_of_eq ?_))
    rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then (b * Real.sqrt (seedR κ)) ^ 2 else 0),
      Finset.sum_ite_eq']
    simp
  have hw : κ₀ / 2 * cnorm w ≤ b * Real.sqrt (seedR κ) := by
    have := hlow.trans hdec
    have h2 : cnorm (fun i => (E i : ℂ) * (x i - chainTheta e m J i *
        cmv (chainA b m J) x i)) = cnorm src := rfl
    linarith
  -- the last coordinate
  set kJ : Fin (J + 1) := ⟨J, by omega⟩
  have hwJ : Real.exp (t * J) * ‖x kJ‖ ≤ cnorm w := by
    have := norm_le_cnorm w kJ
    simp only [w, E, kJ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      at this
    exact this
  have hxJ : ‖m (J + 1) - matchedA e‖ = Real.sqrt ‖chainM m J kJ‖ * ‖x kJ‖ := by
    have hM := norm_pos_iff.mpr (chainM_ne_zero h kJ)
    have hsq := Real.sqrt_pos.mpr hM
    simp only [x, chainX, norm_div, Complex.norm_real, Real.norm_of_nonneg hsq.le]
    unfold chainM
    have hJ : (kJ : ℕ) = J := rfl
    unfold chainM at hsq
    rw [hJ] at hsq ⊢
    field_simp
  rw [hxJ]
  have hsJ : Real.sqrt ‖chainM m J kJ‖ ≤ Real.sqrt (seedR κ) := Real.sqrt_le_sqrt (hbd kJ).2
  have hexp : Real.exp (t * J) * Real.exp (-t * J) = 1 := by
    rw [← Real.exp_add]; simp
  have hxbound : ‖x kJ‖ ≤ 2 / κ₀ * (b * Real.sqrt (seedR κ)) * Real.exp (-t * J) := by
    have h1 : Real.exp (t * J) * ‖x kJ‖ ≤ 2 / κ₀ * (b * Real.sqrt (seedR κ)) := by
      have : cnorm w ≤ 2 / κ₀ * (b * Real.sqrt (seedR κ)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hk]; linarith
      linarith
    have hpos := Real.exp_pos (-t * J)
    calc ‖x kJ‖ = (Real.exp (t * J) * ‖x kJ‖) * Real.exp (-t * J) := by
          rw [mul_comm (Real.exp (t * J)), mul_assoc, hexp, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hpos.le
  have hRs := Real.mul_self_sqrt hR.le
  have hb2 : 2 * b ≤ 1 := by linarith
  calc Real.sqrt ‖chainM m J kJ‖ * ‖x kJ‖
      ≤ Real.sqrt (seedR κ) * (2 / κ₀ * (b * Real.sqrt (seedR κ)) * Real.exp (-t * J)) :=
        mul_le_mul hsJ hxbound (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = (2 * b) * (Real.sqrt (seedR κ) * Real.sqrt (seedR κ)) / κ₀ * Real.exp (-t * J) := by
        ring
    _ ≤ 1 * seedR κ / κ₀ * Real.exp (-t * J) := by
        rw [hRs]; gcongr
    _ = seedConst κ * Real.exp (-seedRate κ * J) := by unfold seedConst; ring

/-- the finite seed bound in existential form: there are `C, c_* > 0`, uniform in `J` and in the
compact parameter set, with `|m_{J+1} - a| ≤ C e^{-c_* J}`. -/
theorem zeroEntrance_finite_seed_exists {κ : ℝ} (hκ : 0 < κ) :
    ∃ C cstar : ℝ, 0 < C ∧ 0 < cstar ∧ ∀ (b e : ℝ) (J : ℕ) (m : ℕ → ℂ), κ ≤ b →
      κ ≤ 1 - 2 * b → κ ≤ 4 - e ^ 2 → IsZeroEntranceChain b e J m →
      ‖m (J + 1) - matchedA e‖ ≤ C * Real.exp (-cstar * J) :=
  ⟨seedConst κ, seedRate κ, (seed_consts_pos hκ).2.2.2.2.2, (seed_consts_pos hκ).2.2.2.2.1,
    fun _ _ _ _ hb hc he h => zeroEntrance_finite_seed hκ hb hc he h⟩

end BlockBand.Endpoints.Clock
