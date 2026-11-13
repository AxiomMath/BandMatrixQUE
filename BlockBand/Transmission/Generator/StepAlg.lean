module

public import BlockBand.Transmission.Generator.PowerCov

/-!
# Deterministic algebra of the `k ≥ 2` one-step expansion in the eigenbasis of `T`

* `gPow hT k = V diag(t^k) V*` (`⪰ 0`, `Re Tr = Σ t_i^k`, `Tr(gPow Z) = Σ t_i^k Z'_{ii}`);
* `trace_diag_mul_sand`: `Tr(diag(d)·sand T Z) = Σ d_i t_i Z'_{ii}`;
* `frobSq_sand_le`: `‖sand T Z‖²_HS ≤ ‖Z‖²·Tr T` (`t ≤ 1`);
* `wsum_quad`: `Σ_{im} t_it_m wsum_j(t_i,t_m) x_ix_m = Σ_{a+b=j}(a+1)(Σ t_i^{a+1}x_i)(Σ t_m^{b+1}x_m)`;
* `norm_sum_pow_fd_le`: `|Σ t_i^n f'_{ii}| ≤ |Tr(Tf)| + √(Tr T)·hs(T,f)` for `n ≥ 1`, `t ≤ 1`;
* `ck_expand`: `c = (1+y)⁻¹`: `|c^{j+2} - 1 + (j+2)yc^j| ≤ (j+2)²y²`, `|c^j - 1| ≤ jy`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ} {Q : Matrix (Fin W) (Fin W) ℂ}

/-- `V diag(t^k) V*`. -/
def gPow (hQ : Q.PosSemidef) (k : ℕ) : Matrix (Fin W) (Fin W) ℂ :=
  ts_U hQ * diagonal (fun i => ((ts_lam hQ i ^ k : ℝ) : ℂ)) * star (ts_U hQ)

theorem gPow_posSemidef (hQ : Q.PosSemidef) (k : ℕ) : (gPow hQ k).PosSemidef := by
  have hd : (diagonal (fun i => ((ts_lam hQ i ^ k : ℝ) : ℂ))).PosSemidef := by
    refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
    exact_mod_cast pow_nonneg (ts_lam_nonneg hQ i) k
  have := hd.mul_mul_conjTranspose_same (ts_U hQ)
  rwa [← Matrix.star_eq_conjTranspose] at this

theorem trace_gPow_mul (hQ : Q.PosSemidef) (k : ℕ) (Z : Matrix (Fin W) (Fin W) ℂ) :
    (gPow hQ k * Z).trace = ∑ i, ((ts_lam hQ i ^ k : ℝ) : ℂ) * ts_ent hQ Z i i := by
  rw [gPow, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, ts_ent_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.mul_assoc, Matrix.mul_diagonal]
  ring

theorem trace_gPow (hQ : Q.PosSemidef) (k : ℕ) :
    (gPow hQ k).trace.re = ∑ i, ts_lam hQ i ^ k := by
  have h := trace_gPow_mul hQ k 1
  rw [Matrix.mul_one] at h
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ts_ent hQ 1 i i = 1 := by
    rw [ts_ent, bilinear, Matrix.one_mulVec]; exact ts_vec_self hQ i
  rw [this, mul_one, Complex.ofReal_re]

theorem trace_diag_mul_sand (hQ : Q.PosSemidef) (d : Fin W → ℂ) (Z : Matrix (Fin W) (Fin W) ℂ) :
    (diagonal d * sand hQ Z).trace = ∑ i, d i * (ts_lam hQ i : ℂ) * ts_ent hQ Z i i := by
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, sand_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.mul_self_sqrt (ts_lam_nonneg hQ i)]; ring

theorem trace_diag_pow (d : Fin W → ℂ) (k : ℕ) : ((diagonal d) ^ k).trace = ∑ i, d i ^ k := by
  rw [diagonal_pow, trace_diagonal]; rfl

theorem ts_ent_one (hQ : Q.PosSemidef) (i : Fin W) : ts_ent hQ 1 i i = 1 := by
  rw [ts_ent, bilinear, Matrix.one_mulVec]; exact ts_vec_self hQ i

theorem frobSq_diagonal_sqrt (hQ : Q.PosSemidef) : frobSq (sqD hQ) = Q.trace.re := by
  rw [frobSq, ← ts_sum_lam hQ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [sqD, diagonal_apply_ne _ (Ne.symm hj)])
    (by simp)]
  simp only [sqD, diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (ts_lam_nonneg hQ i)

/-- `‖sand T Z‖²_HS ≤ ‖Z‖²·Tr T`. -/
theorem frobSq_sand_le (hQ : Q.PosSemidef) (h1 : ∀ i, ts_lam hQ i ≤ 1)
    (Z : Matrix (Fin W) (Fin W) ℂ) : frobSq (sand hQ Z) ≤ ‖Z‖ ^ 2 * Q.trace.re := by
  have hD := norm_sqD_le hQ h1
  have hV : ‖ts_U hQ‖ ≤ 1 := norm_unitary_le (ts_U_star_mul hQ)
  have hV' : ‖star (ts_U hQ)‖ ≤ 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]; exact hV
  have hX : ‖sqD hQ * (star (ts_U hQ) * Z * ts_U hQ)‖ ≤ ‖Z‖ := by
    have hZ := norm_nonneg Z
    calc _ ≤ ‖sqD hQ‖ * (‖star (ts_U hQ)‖ * ‖Z‖ * ‖ts_U hQ‖) := by
          refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
          exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
            (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ 1 * (1 * ‖Z‖ * 1) := by gcongr
      _ = ‖Z‖ := by ring
  rw [sand, ← frobSq_diagonal_sqrt hQ]
  exact (frobSq_mul_left_le _ _).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hX 2) (frobSq_nonneg _))

/-- **Factorisation of the quadratic form.** -/
theorem wsum_quad {n : Type*} [Fintype n] (t : n → ℝ) (x : n → ℂ) (j : ℕ) :
    ∑ i, ∑ m, ((t i * t m * wsum j (t i) (t m) : ℝ) : ℂ) * (x i * x m) =
      ∑ p ∈ antidiagonal j, ((p.1 + 1 : ℕ) : ℂ) * ((∑ i, ((t i ^ (p.1 + 1) : ℝ) : ℂ) * x i) *
        (∑ m, ((t m ^ (p.2 + 1) : ℝ) : ℂ) * x m)) := by
  have hL : ∀ i m, ((t i * t m * wsum j (t i) (t m) : ℝ) : ℂ) * (x i * x m) =
      ∑ p ∈ antidiagonal j, ((p.1 + 1 : ℕ) : ℂ) * ((((t i ^ (p.1 + 1) : ℝ) : ℂ) * x i) *
        (((t m ^ (p.2 + 1) : ℝ) : ℂ) * x m)) := by
    intro i m
    simp only [wsum]; push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  simp_rw [hL, Finset.sum_mul_sum, Finset.mul_sum]
  calc _ = ∑ i, ∑ p ∈ antidiagonal j, ∑ m, ((p.1 + 1 : ℕ) : ℂ) *
        ((((t i ^ (p.1 + 1) : ℝ) : ℂ) * x i) * (((t m ^ (p.2 + 1) : ℝ) : ℂ) * x m)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- `|Σ t_i^n f'_{ii}| ≤ |Tr(Tf)| + √(Tr T)·hs(T,f)`, `n ≥ 1`. -/
theorem norm_sum_pow_fd_le (hQ : Q.PosSemidef) (h1 : ∀ i, ts_lam hQ i ≤ 1)
    (f : Matrix (Fin W) (Fin W) ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ‖∑ i, ((ts_lam hQ i ^ n : ℝ) : ℂ) * ts_ent hQ f i i‖ ≤
      ‖(Q * f).trace‖ + Real.sqrt Q.trace.re * hsSandwich Q f := by
  have hs0 : 0 ≤ Real.sqrt Q.trace.re * hsSandwich Q f :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have : n = 1 := by omega
    subst this
    rw [ts_trace_mul hQ f]
    simp only [pow_one]
    linarith [norm_nonneg ((Q * f).trace)]
  have ht := ts_lam_nonneg hQ
  have hcs : ∑ i, ts_lam hQ i ^ (n - 1) * (ts_lam hQ i * ‖ts_ent hQ f i i‖) ≤
      Real.sqrt (∑ i, (ts_lam hQ i ^ (n - 1)) ^ 2) *
        Real.sqrt (∑ i, (ts_lam hQ i * ‖ts_ent hQ f i i‖) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have ha : ∑ i, (ts_lam hQ i ^ (n - 1)) ^ 2 ≤ Q.trace.re := by
    rw [← ts_sum_lam hQ]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← pow_mul]
    have : 1 ≤ (n - 1) * 2 := by omega
    calc ts_lam hQ i ^ ((n - 1) * 2) ≤ ts_lam hQ i ^ 1 :=
          pow_le_pow_of_le_one (ht i) (h1 i) this
      _ = ts_lam hQ i := pow_one _
  have hb : ∑ i, (ts_lam hQ i * ‖ts_ent hQ f i i‖) ^ 2 ≤ hsSandwich Q f ^ 2 := by
    rw [ts_hs_eq hQ, Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (ht i) (ht j)) (sq_nonneg _))]
    refine Finset.sum_le_sum fun i _ => ?_
    have := Finset.single_le_sum (f := fun j => ts_lam hQ i * ts_lam hQ j * ‖ts_ent hQ f i j‖ ^ 2)
      (fun j _ => mul_nonneg (mul_nonneg (ht i) (ht j)) (sq_nonneg _)) (Finset.mem_univ i)
    nlinarith
  calc ‖∑ i, ((ts_lam hQ i ^ n : ℝ) : ℂ) * ts_ent hQ f i i‖
      ≤ ∑ i, ts_lam hQ i ^ (n - 1) * (ts_lam hQ i * ‖ts_ent hQ f i i‖) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (ht i) n)]
        rw [show n = (n - 1) + 1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        rw [mul_assoc]
    _ ≤ Real.sqrt Q.trace.re * hsSandwich Q f := by
        refine hcs.trans (mul_le_mul (Real.sqrt_le_sqrt ha) ?_ (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _))
        calc Real.sqrt (∑ i, (ts_lam hQ i * ‖ts_ent hQ f i i‖) ^ 2)
            ≤ Real.sqrt (hsSandwich Q f ^ 2) := Real.sqrt_le_sqrt hb
          _ = hsSandwich Q f := Real.sqrt_sq (Real.sqrt_nonneg _)
    _ ≤ _ := le_add_of_nonneg_left (norm_nonneg _)

/-- `c^a - c^{a+n} ≤ n(1 - c)` for `0 ≤ c ≤ 1`. -/
theorem pow_sub_pow_add_le {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) (a n : ℕ) :
    0 ≤ c ^ a - c ^ (a + n) ∧ c ^ a - c ^ (a + n) ≤ n * (1 - c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hca : c ^ (a + n) ≤ 1 := pow_le_one₀ h0 h1
    have e : c ^ (a + (n + 1)) = c ^ (a + n) * c := by rw [← add_assoc, pow_succ]
    constructor
    · rw [e]; nlinarith [pow_nonneg h0 (a + n)]
    · rw [e]; push_cast; nlinarith [pow_nonneg h0 (a + n)]

theorem abs_pow_sub_pow_le {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) (a b : ℕ) :
    |c ^ a - c ^ b| ≤ max a b * (1 - c) := by
  have hc : 0 ≤ 1 - c := by linarith
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
    obtain ⟨h₁, h₂⟩ := pow_sub_pow_add_le h0 h1 a n
    rw [abs_of_nonneg h₁]
    refine h₂.trans (mul_le_mul_of_nonneg_right ?_ hc)
    exact_mod_cast (Nat.le_add_left n a).trans (le_max_right _ _)
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
    obtain ⟨h₁, h₂⟩ := pow_sub_pow_add_le h0 h1 b n
    rw [abs_sub_comm, abs_of_nonneg h₁]
    refine h₂.trans (mul_le_mul_of_nonneg_right ?_ hc)
    exact_mod_cast (Nat.le_add_left n b).trans (le_max_left _ _)

/-- **Scalar expansion of `c^k`**, `c = (1+y)⁻¹`, `y ≥ 0`. -/
theorem ck_expand {y : ℝ} (hy : 0 ≤ y) (j : ℕ) :
    |(1 + y)⁻¹ ^ (j + 2) - 1 + ((j + 2 : ℕ) : ℝ) * y * (1 + y)⁻¹ ^ j| ≤
        ((j + 2 : ℕ) : ℝ) ^ 2 * y ^ 2 ∧
      |(1 + y)⁻¹ ^ j - 1| ≤ j * y := by
  set c := (1 + y)⁻¹
  have hc0 : 0 < c := inv_pos.mpr (by linarith)
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h1c : 1 - c = y * c := by simp only [c]; field_simp; ring
  have h1c' : 1 - c ≤ y := by rw [h1c]; nlinarith
  have hgeom : 1 - c ^ (j + 2) = (1 - c) * ∑ i ∈ range (j + 2), c ^ i := by
    have := geom_sum_mul c (j + 2); linarith
  have e : c ^ (j + 2) - 1 + ((j + 2 : ℕ) : ℝ) * y * c ^ j =
      y * ∑ i ∈ range (j + 2), (c ^ j - c ^ (i + 1)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
    have : ∑ i ∈ range (j + 2), c ^ (i + 1) = c * ∑ i ∈ range (j + 2), c ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have : c ^ (j + 2) - 1 = -(y * c * ∑ i ∈ range (j + 2), c ^ i) := by
      rw [← h1c]; linarith
    rw [this]; ring
  constructor
  · rw [e, abs_mul, abs_of_nonneg hy]
    have hb : ∀ i ∈ range (j + 2), |c ^ j - c ^ (i + 1)| ≤ ((j + 2 : ℕ) : ℝ) * y := by
      intro i hi
      refine (abs_pow_sub_pow_le hc0.le hc1 j (i + 1)).trans ?_
      have hi' := Finset.mem_range.mp hi
      have : ((max j (i + 1) : ℕ) : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
        exact_mod_cast max_le (by omega) (by omega)
      exact mul_le_mul this h1c' (by linarith) (by positivity)
    have := (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)
    rw [Finset.sum_const, card_range, nsmul_eq_mul] at this
    calc y * |∑ i ∈ range (j + 2), (c ^ j - c ^ (i + 1))|
        ≤ y * (((j + 2 : ℕ) : ℝ) * (((j + 2 : ℕ) : ℝ) * y)) := by
          refine mul_le_mul_of_nonneg_left ?_ hy; exact_mod_cast this
      _ = _ := by ring
  · have := abs_pow_sub_pow_le hc0.le hc1 j 0
    rw [pow_zero, max_eq_left (Nat.zero_le j)] at this
    exact this.trans (mul_le_mul_of_nonneg_left h1c' (Nat.cast_nonneg _))

end BlockBand.Transmission.Generator
