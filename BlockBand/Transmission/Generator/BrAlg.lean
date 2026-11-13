module

public import BlockBand.Transmission.Generator.StepInputs
public import BlockBand.Transmission.Generator.StepPoint

/-!
# The one-layer bracket: deterministic algebra

`T ⪰ 0` with eigenvalues `t_i ≤ 1`, eigenvectors `v_i`, `Z'_{im} = v_i*Zv_m` (`ts_ent`),
`D = sand T 1 = diag t`.
* `brLin hT k Z = Σ_i t_i^k Z'_{ii}`; `norm_brLin_le` (`‖·‖ ≤ ‖Z‖ Tr T`, `k ≥ 1`);
  `trace_sandOne_pow_mul` (`Tr(D^n sand T Z) = brLin (n+1) Z`);
* **`br_expand`**: `|Re Tr S^{n+1} - Re Tr D^{n+1} - (n+1) Re brLin (n+1) (U - 1)| ≤
  (n+1)6^{2(n+1)} ‖sand T (U - 1)‖²_HS` for `S = sand T U`, `‖S‖ ≤ 1` (expansion about `D`);
* `ts_ent_one_apply`, `ts_ent_one_sub_apply`, **`br_crossed`**: the passive covariance tensor
  at `(v_i, v_i, v_m, v_m)`; `br_fterm_le` (`Σ_{im} t_i^k t_m^l |f'_{im}||f'_{mi}| ≤ hs(T,f)²`);
* `frobSq_add_le`, **`br_scalar`** (the pointwise remainder of `Δ_kΔ_l`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing BlockBand.Internal.Contracts.Layers
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

theorem frobSq_add_le {n : Type*} [Fintype n] (X Y : Matrix n n ℂ) :
    frobSq (X + Y) ≤ 2 * frobSq X + 2 * frobSq Y := by
  unfold frobSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.add_apply]
  have h := norm_add_le (X i j) (Y i j)
  have h0 := norm_nonneg (X i j + Y i j)
  nlinarith [norm_nonneg (X i j), norm_nonneg (Y i j), sq_nonneg (‖X i j‖ - ‖Y i j‖)]

theorem br_bilinear_conjTranspose {m : Type*} [Fintype m] (u v : m → ℂ) (M : Matrix m m ℂ) :
    bilinear u Mᴴ v = star (bilinear v M u) := by
  simp only [bilinear, dotProduct, mulVec, Matrix.conjTranspose_apply, Pi.star_apply,
    star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ}

/-- `λ_k(Z) = Σ_i t_i^k Z'_{ii}`. -/
def brLin (hT : T.PosSemidef) (k : ℕ) (Z : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  ∑ i, ((ts_lam hT i ^ k : ℝ) : ℂ) * ts_ent hT Z i i

theorem norm_brLin_le (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1) {k : ℕ} (hk : 1 ≤ k)
    (Z : Matrix (Fin W) (Fin W) ℂ) : ‖brLin hT k Z‖ ≤ ‖Z‖ * T.trace.re := by
  rw [← ts_sum_lam hT, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (ts_lam_nonneg hT i) k)]
  calc ts_lam hT i ^ k * ‖ts_ent hT Z i i‖ ≤ ts_lam hT i * ‖Z‖ :=
        mul_le_mul (pow_le_of_le_one (ts_lam_nonneg hT i) (ht1 i) (by omega))
          (ts_norm_ent_le hT Z i i) (norm_nonneg _) (ts_lam_nonneg hT i)
    _ = ‖Z‖ * ts_lam hT i := mul_comm _ _

theorem trace_sandOne_pow_mul (hT : T.PosSemidef) (n : ℕ) (Z : Matrix (Fin W) (Fin W) ℂ) :
    ((sand hT 1) ^ n * sand hT Z).trace = (brLin hT (n + 1) Z) := by
  rw [sand_one, diagonal_pow, trace_diag_mul_sand, brLin]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.pow_apply]
  push_cast; ring

/-- **First-order expansion of `Tr S^{n+1}` about `D = sand T 1`.** -/
theorem br_expand (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (U : Matrix (Fin W) (Fin W) ℂ) (hS : ‖sand hT U‖ ≤ 1) (n : ℕ) :
    |((sand hT U) ^ (n + 1)).trace.re - ((sand hT 1) ^ (n + 1)).trace.re -
        ((n + 1 : ℕ) : ℝ) * (brLin hT (n + 1) (U - 1)).re| ≤
      ((n + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (n + 1)) * frobSq (sand hT (U - 1)) := by
  have hD1 : ‖sand hT 1‖ ≤ 1 := by
    rw [sand_one]
    exact norm_diagonal_le (c := (1 : ℝ)) _ zero_le_one fun i => by
      rw [Complex.norm_real, Real.norm_of_nonneg (ts_lam_nonneg hT i)]; exact ht1 i
  have hB : ‖sand hT (U - 1)‖ ≤ 2 := by
    rw [sand_sub]; exact (norm_sub_le _ _).trans (by linarith)
  have h := pe_first (hD1.trans (by norm_num)) hB (by norm_num : (1 : ℝ) ≤ 2) n
  have e : sand hT 1 + sand hT (U - 1) = sand hT U := by rw [sand_sub]; abel
  rw [e, trace_sandOne_pow_mul] at h
  refine le_trans (le_of_eq ?_) ((Complex.abs_re_le_norm _).trans h)
  simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
    sub_zero]

/-!
## The passive covariance tensor in the eigenbasis
-/

theorem ts_ent_one_apply (hT : T.PosSemidef) (i m : Fin W) :
    ts_ent hT 1 i m = if i = m then 1 else 0 := by
  rw [ts_ent_eq, Matrix.mul_one, ts_U_star_mul, Matrix.one_apply]

theorem ts_ent_self_apply (hT : T.PosSemidef) (i m : Fin W) :
    ts_ent hT T i m = if i = m then (ts_lam hT i : ℂ) else 0 := by
  have h := ts_spectral hT
  have e : star (ts_U hT) * T * ts_U hT = diagonal fun i => (ts_lam hT i : ℂ) := by
    calc star (ts_U hT) * T * ts_U hT =
        star (ts_U hT) * (ts_U hT * diagonal (fun i => (ts_lam hT i : ℂ)) * star (ts_U hT)) *
          ts_U hT := by rw [← h]
      _ = (star (ts_U hT) * ts_U hT) * diagonal (fun i => (ts_lam hT i : ℂ)) *
          (star (ts_U hT) * ts_U hT) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [ts_U_star_mul, Matrix.one_mul, Matrix.mul_one]
  rw [ts_ent_eq, e, diagonal_apply]

theorem ts_ent_one_sub_apply (hT : T.PosSemidef) (i m : Fin W) :
    ts_ent hT (1 - T) i m = if i = m then 1 - (ts_lam hT i : ℂ) else 0 := by
  have e : ts_ent hT (1 - T) i m = ts_ent hT 1 i m - ts_ent hT T i m := by
    simp only [ts_ent, bilinear_sub]
  rw [e, ts_ent_one_apply, ts_ent_self_apply]
  split_ifs <;> simp

/-- **The passive covariance tensor at `(v_i, v_i, v_m, v_m)`.** -/
theorem br_crossed (hT : T.PosSemidef) (f : Matrix (Fin W) (Fin W) ℂ) (a σ σ' : ℂ)
    (i m : Fin W) :
    a * (crossedTensor (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) 1 (1 - T) +
        crossedTensor (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) (1 - T) 1) +
      σ * crossedTensor (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) f f +
      σ' * crossedTensor (ts_vec hT i) (ts_vec hT i) (ts_vec hT m) (ts_vec hT m) fᴴ fᴴ =
    (if i = m then a * (2 * (1 - (ts_lam hT i : ℂ))) else 0) +
      σ * (ts_ent hT f i m * ts_ent hT f m i) +
      σ' * (conj (ts_ent hT f m i) * conj (ts_ent hT f i m)) := by
  have e1 : ∀ Z : Matrix (Fin W) (Fin W) ℂ, ∀ p q : Fin W,
      bilinear (ts_vec hT p) Z (ts_vec hT q) = ts_ent hT Z p q := fun _ _ _ => rfl
  have e2 : ∀ p q : Fin W, bilinear (ts_vec hT p) fᴴ (ts_vec hT q) = conj (ts_ent hT f q p) :=
    fun p q => br_bilinear_conjTranspose _ _ _
  simp only [crossedTensor, e2, e1, ts_ent_one_apply, ts_ent_one_sub_apply]
  by_cases h : i = m
  · subst h; simp only [↓reduceIte]; ring
  · have h' : m ≠ i := Ne.symm h
    simp [h, h']

/-- **The `f`-terms**: `Σ_{im} t_i^k t_m^l |f'_{im}||f'_{mi}| ≤ hs(T,f)²` (`k, l ≥ 1`). -/
theorem br_fterm_le (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1) {k l : ℕ} (hk : 1 ≤ k)
    (hl : 1 ≤ l) (f : Matrix (Fin W) (Fin W) ℂ) :
    ∑ i, ∑ m, ts_lam hT i ^ k * ts_lam hT m ^ l * (‖ts_ent hT f i m‖ * ‖ts_ent hT f m i‖) ≤
      hsSandwich T f ^ 2 := by
  have hs : hsSandwich T f ^ 2 = ∑ i, ∑ m, ts_lam hT i * ts_lam hT m * ‖ts_ent hT f i m‖ ^ 2 := by
    rw [ts_hs_eq hT, Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (ts_lam_nonneg hT i) (ts_lam_nonneg hT j)) (sq_nonneg _))]
  have hswap : ∑ i, ∑ m, ts_lam hT i * ts_lam hT m * ‖ts_ent hT f m i‖ ^ 2 =
      hsSandwich T f ^ 2 := by
    rw [hs, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
  have hpt : ∀ i m, ts_lam hT i ^ k * ts_lam hT m ^ l *
      (‖ts_ent hT f i m‖ * ‖ts_ent hT f m i‖) ≤
      (ts_lam hT i * ts_lam hT m * ‖ts_ent hT f i m‖ ^ 2 +
        ts_lam hT i * ts_lam hT m * ‖ts_ent hT f m i‖ ^ 2) / 2 := by
    intro i m
    have h0 := mul_nonneg (ts_lam_nonneg hT i) (ts_lam_nonneg hT m)
    have hw : ts_lam hT i ^ k * ts_lam hT m ^ l ≤ ts_lam hT i * ts_lam hT m :=
      mul_le_mul (pow_le_of_le_one (ts_lam_nonneg hT i) (ht1 i) (by omega))
        (pow_le_of_le_one (ts_lam_nonneg hT m) (ht1 m) (by omega))
        (pow_nonneg (ts_lam_nonneg hT m) l) (ts_lam_nonneg hT i)
    have hab : ‖ts_ent hT f i m‖ * ‖ts_ent hT f m i‖ ≤
        (‖ts_ent hT f i m‖ ^ 2 + ‖ts_ent hT f m i‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖ts_ent hT f i m‖ - ‖ts_ent hT f m i‖)]
    have hn : 0 ≤ ‖ts_ent hT f i m‖ * ‖ts_ent hT f m i‖ := by positivity
    calc ts_lam hT i ^ k * ts_lam hT m ^ l * (‖ts_ent hT f i m‖ * ‖ts_ent hT f m i‖) ≤
        ts_lam hT i * ts_lam hT m * (‖ts_ent hT f i m‖ * ‖ts_ent hT f m i‖) :=
          mul_le_mul_of_nonneg_right hw hn
      _ ≤ ts_lam hT i * ts_lam hT m * ((‖ts_ent hT f i m‖ ^ 2 + ‖ts_ent hT f m i‖ ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hab h0
      _ = _ := by ring
  calc _ ≤ ∑ i, ∑ m, (ts_lam hT i * ts_lam hT m * ‖ts_ent hT f i m‖ ^ 2 +
        ts_lam hT i * ts_lam hT m * ‖ts_ent hT f m i‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => hpt i m
    _ = ((∑ i, ∑ m, ts_lam hT i * ts_lam hT m * ‖ts_ent hT f i m‖ ^ 2) +
        ∑ i, ∑ m, ts_lam hT i * ts_lam hT m * ‖ts_ent hT f m i‖ ^ 2) / 2 := by
        simp only [← Finset.sum_div, ← Finset.sum_add_distrib]
    _ = _ := by rw [hswap, ← hs]; ring

/-!
## The pointwise remainder
-/

theorem br_yo {s : ℝ} (hs : 0 < s) (x y : ℝ) : 2 * |x| * y ≤ x ^ 2 / s + s * y ^ 2 := by
  have key : x ^ 2 / s + s * y ^ 2 - 2 * |x| * y = (|x| - s * y) ^ 2 / s := by
    rw [← sq_abs x]; field_simp; ring
  have : 0 ≤ (|x| - s * y) ^ 2 / s := div_nonneg (sq_nonneg _) hs.le
  linarith

theorem br_young {s h n : ℝ} (hs : 0 < s) (x : ℝ) :
    |x| * (2 * h + 2 * n) ≤ 2 * x ^ 2 / s + s * (h ^ 2 + n ^ 2) := by
  have h1 := br_yo hs x h
  have h2 := br_yo hs x n
  have e1 : |x| * (2 * h + 2 * n) = 2 * |x| * h + 2 * |x| * n := by ring
  have e2 : 2 * x ^ 2 / s + s * (h ^ 2 + n ^ 2) =
      (x ^ 2 / s + s * h ^ 2) + (x ^ 2 / s + s * n ^ 2) := by ring
  rw [e1, e2]; linarith

theorem br_sqR {R c h n : ℝ} (hR : |R| ≤ c * (2 * h + 2 * n)) :
    R ^ 2 ≤ 8 * c ^ 2 * (h ^ 2 + n ^ 2) := by
  have h1 := pow_le_pow_left₀ (abs_nonneg R) hR 2
  rw [sq_abs] at h1
  have hhn : (h + n) ^ 2 ≤ 2 * (h ^ 2 + n ^ 2) := by
    have := sq_nonneg (h - n)
    have e : 2 * (h ^ 2 + n ^ 2) - (h + n) ^ 2 = (h - n) ^ 2 := by ring
    linarith
  calc R ^ 2 ≤ (c * (2 * h + 2 * n)) ^ 2 := h1
    _ = 4 * c ^ 2 * (h + n) ^ 2 := by ring
    _ ≤ 4 * c ^ 2 * (2 * (h ^ 2 + n ^ 2)) := by gcongr
    _ = _ := by ring

theorem br_sqb {b B : ℝ} (hb : |b| ≤ B) : b ^ 2 ≤ B ^ 2 := by
  have := pow_le_pow_left₀ (abs_nonneg b) hb 2; rwa [sq_abs] at this

theorem br_abs_mul_le (x y : ℝ) : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  rw [abs_mul, ← sq_abs x, ← sq_abs y]
  have := sq_nonneg (|x| - |y|)
  have e : (|x| ^ 2 + |y| ^ 2) / 2 - |x| * |y| = (|x| - |y|) ^ 2 / 2 := by ring
  linarith

theorem br_sq_add_le (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  have := sq_nonneg (x - y)
  have e : 2 * x ^ 2 + 2 * y ^ 2 - (x + y) ^ 2 = (x - y) ^ 2 := by ring
  linarith

/-- **Pointwise remainder of the bracket.** With `Δ_k = x_k + b_k + R_k`, `|b_k| ≤ B_k`,
`|R_k| ≤ c_k(2h + 2n)`: `|Δ_kΔ_l - x_kx_l - x_kb_l - b_kx_l|` is at most the displayed sum. -/
theorem br_scalar {Δk Δl xk xl bk bl Rk Rl h n s ck cl Bk Bl : ℝ} (hΔk : Δk = xk + bk + Rk)
    (hΔl : Δl = xl + bl + Rl) (hbk : |bk| ≤ Bk) (hbl : |bl| ≤ Bl)
    (hRk : |Rk| ≤ ck * (2 * h + 2 * n)) (hRl : |Rl| ≤ cl * (2 * h + 2 * n))
    (hs : 0 < s) (hck : 0 ≤ ck) (hcl : 0 ≤ cl) :
    |Δk * Δl - xk * xl - xk * bl - bk * xl| ≤
      cl * (2 * xk ^ 2 / s + s * (h ^ 2 + n ^ 2)) + ck * (2 * xl ^ 2 / s + s * (h ^ 2 + n ^ 2)) +
        (Bk ^ 2 + Bl ^ 2) + 8 * (ck ^ 2 + cl ^ 2) * (h ^ 2 + n ^ 2) := by
  have e : Δk * Δl - xk * xl - xk * bl - bk * xl = xk * Rl + Rk * xl + (bk + Rk) * (bl + Rl) := by
    rw [hΔk, hΔl]; ring
  rw [e]
  have t1 : |xk * Rl| ≤ cl * (2 * xk ^ 2 / s + s * (h ^ 2 + n ^ 2)) := by
    rw [abs_mul]
    calc |xk| * |Rl| ≤ |xk| * (cl * (2 * h + 2 * n)) :=
          mul_le_mul_of_nonneg_left hRl (abs_nonneg _)
      _ = cl * (|xk| * (2 * h + 2 * n)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (br_young hs xk) hcl
  have t2 : |Rk * xl| ≤ ck * (2 * xl ^ 2 / s + s * (h ^ 2 + n ^ 2)) := by
    rw [abs_mul]
    calc |Rk| * |xl| ≤ (ck * (2 * h + 2 * n)) * |xl| :=
          mul_le_mul_of_nonneg_right hRk (abs_nonneg _)
      _ = ck * (|xl| * (2 * h + 2 * n)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (br_young hs xl) hck
  have q1 := br_sqR hRk
  have q2 := br_sqR hRl
  have b1 := br_sqb hbk
  have b2 := br_sqb hbl
  have a1 := br_abs_mul_le (bk + Rk) (bl + Rl)
  have a2 := br_sq_add_le bk Rk
  have a3 := br_sq_add_le bl Rl
  have e8 : 8 * (ck ^ 2 + cl ^ 2) * (h ^ 2 + n ^ 2) =
      8 * ck ^ 2 * (h ^ 2 + n ^ 2) + 8 * cl ^ 2 * (h ^ 2 + n ^ 2) := by ring
  have t3 : |(bk + Rk) * (bl + Rl)| ≤ (Bk ^ 2 + Bl ^ 2) + 8 * (ck ^ 2 + cl ^ 2) * (h ^ 2 + n ^ 2) := by
    rw [e8]; linarith
  have t0 := abs_add_le (xk * Rl + Rk * xl) ((bk + Rk) * (bl + Rl))
  have t00 := abs_add_le (xk * Rl) (Rk * xl)
  linarith

end BlockBand.Transmission.Generator
