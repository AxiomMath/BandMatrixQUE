module

public import BlockBand.Native.ErdosRiabov.Kernel.ProfilePow
public import BlockBand.Native.ErdosRiabov.Kernel.Semicircle

/-!
# Variance-scaling kernels and their algebra

The kernels `A_t = Y(1 - tY)⁻¹` and propagators `P̂_{s,t}` of the variance-scaling flow and their
algebraic and differential identities.

Setting: `S` a real `N × N` matrix that is entrywise nonnegative, symmetric and row-stochastic
(`StochasticSymm`; `shortRingProfile b m W` is one for `0 < b < 1/2`, `m ≥ 3`, `W ≥ 1`:
`shortRingProfile_stochasticSymm`). `S_ℂ = S.map (algebraMap ℝ ℂ)`.
For `μ, μ' ∈ ℂ`, `Y = μμ' S_ℂ` (`vsY`), and

* `vsKernel S μ μ' t = A_t = Y (1 - tY)⁻¹`,
* `vsPropagator S μ μ' s t = P̂_{s,t} = (1 - sY)(1 - tY)⁻¹`,
* `vsPi N = Π = 𝟙𝟙ᵀ/N`.

`vsKernel_algebra` (for `|μ|, |μ'| < 1`, `s, t ∈ [0,1]`, `c = μμ'`) collects:
Neumann series
`A_t = Σ_k t^k Y^{k+1}` (entrywise, absolutely convergent); `P̂_{s,t} = I + (t-s)A_t`,
`P̂_{s,s} = I`; `A_t = P̂_{s,t} A_s`; resolvent identity `A_t - A_s = (t-s) A_t A_s`;
`∂_t A_t = A_t²` and `∂_t P̂_{s,t} = A_t P̂_{s,t}` (entrywise); symmetry; commutation of `A_t` with
`S_ℂ` and with every other kernel `A_r(ν,ν')` (`|ν|, |ν'| < 1`, `r ∈ [0,1]`); row sums
`A_t 𝟙 = c/(1-tc) 𝟙`, `P̂_{s,t} 𝟙 = (1-sc)/(1-tc) 𝟙`; `Π A_t = A_t Π = c/(1-tc) Π`; and, for
`μ' = conj μ`, `A_t ≥ 0` entrywise (real, nonnegative).

With `Π = 𝟙𝟙ᵀ/N` the saturated kernel satisfies `Π T̂_t = T̂_t Π = (Im m/η_t) Π`; each entry of
this matrix is `Im m/(N η_t)`.

The propagator `P̂` is the closed form `(1-sY)(1-tY)⁻¹`, characterized by `P̂_{s,s} = I` and
`∂_t P̂_{s,t} = A_t P̂_{s,t}`; it is used in this closed form, not as `exp ∫_s^t T̂_r dr`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Kernel

open Matrix BlockBand.Internal.Contracts.Inputs BlockBand.Adapters.ErdosRiabov
open BlockBand.External.ErdosRiabov (semicircleM semicircleM_dyson norm_semicircleM_lt_one)
open scoped BigOperators ComplexConjugate

variable {N : ℕ}

/-!
## Stochastic symmetric profiles
-/

/-- Entrywise nonnegative, symmetric, row-stochastic real matrix. -/
structure StochasticSymm (S : Matrix (Fin N) (Fin N) ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ S x y
  symm : ∀ x y, S x y = S y x
  rowSum : ∀ x, ∑ y, S x y = 1

/-- The short-ring profile is stochastic symmetric (`0 < b < 1/2`, `m ≥ 3`, `W ≥ 1`). -/
theorem shortRingProfile_stochasticSymm {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {m W : ℕ}
    (hm : 3 ≤ m) (hW : 0 < W) : StochasticSymm (shortRingProfile b m W) where
  nonneg := shortRingProfile_nonneg hb0 hb m W
  symm := shortRingProfile_symm b m W
  rowSum := shortRingProfile_rowSum b hm hW

namespace StochasticSymm

variable {S : Matrix (Fin N) (Fin N) ℝ}

theorem pow_nonneg (hS : StochasticSymm S) (k : ℕ) (x y : Fin N) : 0 ≤ (S ^ k) x y := by
  induction k generalizing y with
  | zero =>
    rw [_root_.pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih z) (hS.nonneg z y)

theorem pow_rowSum (hS : StochasticSymm S) (k : ℕ) (x : Fin N) : ∑ y, (S ^ k) x y = 1 := by
  induction k with
  | zero =>
    simp only [_root_.pow_zero, Matrix.one_apply]
    rw [Finset.sum_ite_eq]
    simp
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hS.rowSum, mul_one]
    exact ih

theorem pow_le_one (hS : StochasticSymm S) (k : ℕ) (x y : Fin N) : (S ^ k) x y ≤ 1 := by
  calc (S ^ k) x y ≤ ∑ j, (S ^ k) x j :=
        Finset.single_le_sum (fun j _ => hS.pow_nonneg k x j) (Finset.mem_univ y)
    _ = 1 := hS.pow_rowSum k x

end StochasticSymm

/-!
## Definitions
-/

/-- `S_ℂ`: the profile as a complex matrix. -/
def cMat (S : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℂ := S.map (algebraMap ℝ ℂ)

/-- `Y = μμ' S`. -/
def vsY (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (μ * μ') • cMat S

/-- The kernel `A_t(ζ,ζ') = Y(1 - tY)⁻¹`, `Y = μμ'S`, `μ = m(ζ)`, `μ' = m(ζ')`. -/
def vsKernel (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  vsY S μ μ' * (1 - (t : ℂ) • vsY S μ μ')⁻¹

/-- VS propagator in closed form `P̂_{s,t} = (1 - sY)(1 - tY)⁻¹`. -/
def vsPropagator (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (s t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (1 - (s : ℂ) • vsY S μ μ') * (1 - (t : ℂ) • vsY S μ μ')⁻¹

/-- The constant-mode projection `Π = 𝟙𝟙ᵀ/N`. -/
def vsPi (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := fun _ _ => (N : ℂ)⁻¹

theorem cMat_apply (S : Matrix (Fin N) (Fin N) ℝ) (x y : Fin N) :
    cMat S x y = (S x y : ℂ) := by
  simp [cMat]

theorem cMat_pow (S : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) : cMat S ^ k = cMat (S ^ k) :=
  (Matrix.map_pow S (algebraMap ℝ ℂ) k).symm

theorem cMat_one : cMat (1 : Matrix (Fin N) (Fin N) ℝ) = 1 := by
  ext x y
  rw [cMat_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem smul_vsY (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (t : ℝ) :
    (t : ℂ) • vsY S μ μ' = ((t : ℂ) * (μ * μ')) • cMat S := by
  rw [vsY, smul_smul]

/-!
## The Neumann matrix
-/

/-- `G(a)_{xy} = Σ_k a^k (S^k)_{xy}`. -/
def neumann (S : Matrix (Fin N) (Fin N) ℝ) (a : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun x y => ∑' k : ℕ, a ^ k * ((S ^ k) x y : ℂ)

variable {S : Matrix (Fin N) (Fin N) ℝ}

theorem norm_term_le (hS : StochasticSymm S) (a : ℂ) (k : ℕ) (x y : Fin N) :
    ‖a ^ k * ((S ^ k) x y : ℂ)‖ ≤ ‖a‖ ^ k := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hS.pow_nonneg k x y)]
  exact mul_le_of_le_one_right (_root_.pow_nonneg (norm_nonneg _) _) (hS.pow_le_one k x y)

theorem summable_norm_term (hS : StochasticSymm S) {a : ℂ} (ha : ‖a‖ < 1) (j : ℕ)
    (x y : Fin N) : Summable (fun k => ‖a ^ k * ((S ^ (k + j)) x y : ℂ)‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    (summable_geometric_of_lt_one (norm_nonneg a) ha)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hS.pow_nonneg _ x y)]
  exact mul_le_of_le_one_right (_root_.pow_nonneg (norm_nonneg _) _) (hS.pow_le_one _ x y)

theorem summable_term (hS : StochasticSymm S) {a : ℂ} (ha : ‖a‖ < 1) (j : ℕ) (x y : Fin N) :
    Summable (fun k => a ^ k * ((S ^ (k + j)) x y : ℂ)) :=
  (summable_norm_term hS ha j x y).of_norm

/-- `Σ_z S_{xz} G(a)_{zy} = Σ_k a^k (S^{k+1})_{xy}`. -/
theorem sum_mul_neumann (hS : StochasticSymm S) {a : ℂ} (ha : ‖a‖ < 1) (x y : Fin N) :
    ∑ z, cMat S x z * neumann S a z y = ∑' k : ℕ, a ^ k * ((S ^ (k + 1)) x y : ℂ) := by
  have hsum : ∀ z ∈ (Finset.univ : Finset (Fin N)),
      Summable (fun k : ℕ => cMat S x z * (a ^ k * ((S ^ k) z y : ℂ))) := fun z _ =>
    (by simpa using summable_term hS ha 0 z y : Summable _).mul_left _
  calc ∑ z, cMat S x z * neumann S a z y
      = ∑ z, ∑' k : ℕ, cMat S x z * (a ^ k * ((S ^ k) z y : ℂ)) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [neumann, tsum_mul_left]
    _ = ∑' k : ℕ, ∑ z, cMat S x z * (a ^ k * ((S ^ k) z y : ℂ)) :=
        (Summable.tsum_finsetSum hsum).symm
    _ = _ := by
        congr 1
        funext k
        rw [pow_succ', Matrix.mul_apply, Complex.ofReal_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [cMat_apply, Complex.ofReal_mul]
        ring

theorem one_sub_smul_mul_neumann (hS : StochasticSymm S) {a : ℂ} (ha : ‖a‖ < 1) :
    (1 - a • cMat S) * neumann S a = 1 := by
  ext x y
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.mul_apply, sum_mul_neumann hS ha, smul_eq_mul, ← tsum_mul_left]
  have h0 := summable_term hS ha 0 x y
  simp only [add_zero] at h0
  rw [neumann, h0.tsum_eq_zero_add]
  have h1 : ((S ^ 0) x y : ℂ) = (1 : Matrix (Fin N) (Fin N) ℂ) x y := by
    rw [_root_.pow_zero, ← cMat_apply, cMat_one]
  rw [h1]
  have h2 : ∀ k : ℕ, a ^ (k + 1) * ((S ^ (k + 1)) x y : ℂ) =
      a * (a ^ k * ((S ^ (k + 1)) x y : ℂ)) := fun k => by ring
  simp_rw [h2]
  ring

theorem inv_one_sub_smul (hS : StochasticSymm S) {a : ℂ} (ha : ‖a‖ < 1) :
    (1 - a • cMat S)⁻¹ = neumann S a :=
  Matrix.inv_eq_right_inv (one_sub_smul_mul_neumann hS ha)

theorem one_sub_smul_mul_inv (hS : StochasticSymm S) {a : ℂ} (ha : ‖a‖ < 1) :
    (1 - a • cMat S) * (1 - a • cMat S)⁻¹ = 1 := by
  rw [inv_one_sub_smul hS ha]
  exact one_sub_smul_mul_neumann hS ha

theorem inv_mul_one_sub_smul (hS : StochasticSymm S) {a : ℂ} (ha : ‖a‖ < 1) :
    (1 - a • cMat S)⁻¹ * (1 - a • cMat S) = 1 := by
  rw [inv_one_sub_smul hS ha]
  exact mul_eq_one_comm.mp (one_sub_smul_mul_neumann hS ha)

theorem rowSum_neumann (hS : StochasticSymm S) {a : ℂ} (ha : ‖a‖ < 1) (x : Fin N) :
    ∑ y, neumann S a x y = (1 - a)⁻¹ := by
  have hsum : ∀ y ∈ (Finset.univ : Finset (Fin N)),
      Summable (fun k : ℕ => a ^ k * ((S ^ k) x y : ℂ)) := fun y _ => by
    simpa using summable_term hS ha 0 x y
  simp only [neumann]
  rw [← Summable.tsum_finsetSum hsum, ← tsum_geometric_of_norm_lt_one ha]
  congr 1
  funext k
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, hS.pow_rowSum, Complex.ofReal_one, mul_one]

/-!
## Commutation
-/

/-- A matrix commuting with `B` commutes with a two-sided inverse of `B`. -/
theorem commute_inv_of_commute {M B Binv : Matrix (Fin N) (Fin N) ℂ} (hl : B * Binv = 1)
    (hr : Binv * B = 1) (hc : Commute M B) : Commute M Binv := by
  show M * Binv = Binv * M
  calc M * Binv = (Binv * B) * (M * Binv) := by rw [hr, Matrix.one_mul]
    _ = Binv * (B * M) * Binv := by simp only [Matrix.mul_assoc]
    _ = Binv * (M * B) * Binv := by rw [hc.eq]
    _ = Binv * M * (B * Binv) := by simp only [Matrix.mul_assoc]
    _ = Binv * M := by rw [hl, Matrix.mul_one]

theorem commute_one_sub_smul {M : Matrix (Fin N) (Fin N) ℂ} (hM : Commute M (cMat S)) (a : ℂ) :
    Commute M (1 - a • cMat S) :=
  (Commute.one_right M).sub_right (hM.smul_right a)

theorem commute_inv_one_sub_smul (hS : StochasticSymm S) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : Commute M (cMat S)) {a : ℂ} (ha : ‖a‖ < 1) : Commute M (1 - a • cMat S)⁻¹ :=
  commute_inv_of_commute (one_sub_smul_mul_inv hS ha) (inv_mul_one_sub_smul hS ha)
    (commute_one_sub_smul hM a)

/-- Every kernel commutes with `S_ℂ`. -/
theorem commute_cMat_vsKernel (hS : StochasticSymm S) {μ μ' : ℂ} {t : ℝ}
    (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) : Commute (cMat S) (vsKernel S μ μ' t) := by
  unfold vsKernel
  rw [smul_vsY]
  exact ((Commute.refl _).smul_right _).mul_right
    (commute_inv_one_sub_smul hS (Commute.refl _) ht)

/-- A matrix commuting with `S_ℂ` commutes with every kernel. -/
theorem commute_vsKernel_of_commute (hS : StochasticSymm S) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : Commute M (cMat S)) {μ μ' : ℂ} {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    Commute M (vsKernel S μ μ' t) := by
  unfold vsKernel
  rw [smul_vsY]
  exact (hM.smul_right _).mul_right (commute_inv_one_sub_smul hS hM ht)

/-!
## Algebraic identities
-/

theorem one_sub_ne_zero {a : ℂ} (ha : ‖a‖ < 1) : 1 - a ≠ 0 := by
  intro h
  have : a = 1 := by linear_combination -h
  rw [this, norm_one] at ha
  exact lt_irrefl _ ha

section Identities

variable (hS : StochasticSymm S) {μ μ' : ℂ}
include hS

/-- `R_t := (1-tY)⁻¹` is a right inverse. -/
theorem one_sub_vsY_mul_inv {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    (1 - (t : ℂ) • vsY S μ μ') * (1 - (t : ℂ) • vsY S μ μ')⁻¹ = 1 := by
  rw [smul_vsY]
  exact one_sub_smul_mul_inv hS ht

theorem inv_mul_one_sub_vsY {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    (1 - (t : ℂ) • vsY S μ μ')⁻¹ * (1 - (t : ℂ) • vsY S μ μ') = 1 := by
  rw [smul_vsY]
  exact inv_mul_one_sub_smul hS ht

theorem commute_vsY_inv {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    Commute (vsY S μ μ') (1 - (t : ℂ) • vsY S μ μ')⁻¹ := by
  rw [smul_vsY]
  exact commute_inv_one_sub_smul hS ((Commute.refl _).smul_left _) ht

/-- `P̂_{s,t} = I + (t-s) A_t`. -/
theorem vsPropagator_eq {s t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    vsPropagator S μ μ' s t = 1 + ((t : ℂ) - s) • vsKernel S μ μ' t := by
  unfold vsPropagator vsKernel
  have hsplit : (1 - (s : ℂ) • vsY S μ μ') =
      (1 - (t : ℂ) • vsY S μ μ') + ((t : ℂ) - s) • vsY S μ μ' := by
    rw [sub_smul]
    abel
  rw [hsplit, Matrix.add_mul, one_sub_vsY_mul_inv hS ht, Matrix.smul_mul]

theorem vsPropagator_self {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    vsPropagator S μ μ' t t = 1 := by
  rw [vsPropagator_eq hS ht, sub_self, zero_smul, add_zero]

/-- Resolvent identity `A_t - A_s = (t-s) A_t A_s`. -/
theorem vsKernel_sub {s t : ℝ} (hs : ‖(s : ℂ) * (μ * μ')‖ < 1)
    (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    vsKernel S μ μ' t - vsKernel S μ μ' s =
      ((t : ℂ) - s) • (vsKernel S μ μ' t * vsKernel S μ μ' s) := by
  unfold vsKernel
  set Y := vsY S μ μ'
  set Rt := (1 - (t : ℂ) • Y)⁻¹
  set Rs := (1 - (s : ℂ) • Y)⁻¹
  have hRt : Rt * (1 - (t : ℂ) • Y) = 1 := inv_mul_one_sub_vsY hS ht
  have hRs : (1 - (s : ℂ) • Y) * Rs = 1 := one_sub_vsY_mul_inv hS hs
  have hres : Rt - Rs = ((t : ℂ) - s) • (Rt * Y * Rs) := by
    have e1 : Rt = Rt * (1 - (s : ℂ) • Y) * Rs := by rw [Matrix.mul_assoc, hRs, Matrix.mul_one]
    have e2 : Rs = Rt * (1 - (t : ℂ) • Y) * Rs := by rw [hRt, Matrix.one_mul]
    calc Rt - Rs = Rt * (1 - (s : ℂ) • Y) * Rs - Rt * (1 - (t : ℂ) • Y) * Rs := by
          rw [← e1, ← e2]
      _ = Rt * ((1 - (s : ℂ) • Y) - (1 - (t : ℂ) • Y)) * Rs := by
          rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      _ = ((t : ℂ) - s) • (Rt * Y * Rs) := by
          have : (1 - (s : ℂ) • Y) - (1 - (t : ℂ) • Y) = ((t : ℂ) - s) • Y := by
            rw [sub_smul]; abel
          rw [this, Matrix.mul_smul, Matrix.smul_mul]
  calc Y * Rt - Y * Rs = Y * (Rt - Rs) := (Matrix.mul_sub _ _ _).symm
    _ = ((t : ℂ) - s) • (Y * Rt * (Y * Rs)) := by
        rw [hres, Matrix.mul_smul]
        simp only [Matrix.mul_assoc]

/-- `A_t = P̂_{s,t} A_s`. -/
theorem vsKernel_eq_propagator_mul {s t : ℝ} (hs : ‖(s : ℂ) * (μ * μ')‖ < 1)
    (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    vsKernel S μ μ' t = vsPropagator S μ μ' s t * vsKernel S μ μ' s := by
  rw [vsPropagator_eq hS ht, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
    ← vsKernel_sub hS hs ht]
  abel

/-- `A_t` is symmetric. -/
theorem vsKernel_transpose {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    (vsKernel S μ μ' t)ᵀ = vsKernel S μ μ' t := by
  have hcT : (cMat S)ᵀ = cMat S := by
    ext x y
    rw [Matrix.transpose_apply, cMat_apply, cMat_apply, hS.symm]
  have hYT : (vsY S μ μ')ᵀ = vsY S μ μ' := by rw [vsY, Matrix.transpose_smul, hcT]
  unfold vsKernel
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_smul, hYT]
  exact ((commute_vsY_inv hS ht).eq).symm

theorem vsKernel_symm {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) (x y : Fin N) :
    vsKernel S μ μ' t x y = vsKernel S μ μ' t y x := by
  rw [← Matrix.transpose_apply (vsKernel S μ μ' t) y x, vsKernel_transpose hS ht]

/-- Entry formula: `(A_t)_{xy} = c Σ_k (tc)^k (S^{k+1})_{xy}`, `c = μμ'`. -/
theorem vsKernel_apply {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) (x y : Fin N) :
    vsKernel S μ μ' t x y =
      (μ * μ') * ∑' k : ℕ, ((t : ℂ) * (μ * μ')) ^ k * ((S ^ (k + 1)) x y : ℂ) := by
  unfold vsKernel
  rw [smul_vsY, inv_one_sub_smul hS ht, vsY, Matrix.smul_mul, Matrix.smul_apply,
    Matrix.mul_apply, sum_mul_neumann hS ht, smul_eq_mul]

/-- **Neumann series**: `(A_t)_{xy} = Σ_k (t^k Y^{k+1})_{xy}`, absolutely convergent. -/
theorem vsKernel_hasSum {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) (x y : Fin N) :
    Summable (fun k : ℕ => ‖((t : ℂ) ^ k • vsY S μ μ' ^ (k + 1)) x y‖) ∧
      HasSum (fun k : ℕ => ((t : ℂ) ^ k • vsY S μ μ' ^ (k + 1)) x y)
        (vsKernel S μ μ' t x y) := by
  have hterm : ∀ k : ℕ, ((t : ℂ) ^ k • vsY S μ μ' ^ (k + 1)) x y =
      (μ * μ') * (((t : ℂ) * (μ * μ')) ^ k * ((S ^ (k + 1)) x y : ℂ)) := fun k => by
    rw [vsY, smul_pow, cMat_pow, Matrix.smul_apply, Matrix.smul_apply, cMat_apply,
      smul_eq_mul, smul_eq_mul]
    ring
  simp_rw [hterm]
  refine ⟨?_, ?_⟩
  · exact ((summable_norm_term hS ht 1 x y).mul_left ‖μ * μ'‖).congr
      (fun k => (norm_mul _ _).symm)
  · rw [vsKernel_apply hS ht, ← tsum_mul_left]
    exact ((summable_term hS ht 1 x y).mul_left _).hasSum

/-- Row sums: `Σ_y (A_t)_{xy} = c/(1 - tc)`, `c = μμ'`. -/
theorem vsKernel_rowSum {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) (x : Fin N) :
    ∑ y, vsKernel S μ μ' t x y = (μ * μ') / (1 - (t : ℂ) * (μ * μ')) := by
  unfold vsKernel
  rw [smul_vsY, inv_one_sub_smul hS ht, vsY]
  simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  have hc1 : ∑ z, cMat S x z = 1 := by
    simp_rw [cMat_apply]
    rw [← Complex.ofReal_sum, hS.rowSum, Complex.ofReal_one]
  calc ∑ y, ∑ z, μ * μ' * cMat S x z * neumann S ((t : ℂ) * (μ * μ')) z y
      = μ * μ' * ∑ z, ∑ y, cMat S x z * neumann S ((t : ℂ) * (μ * μ')) z y := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum, mul_assoc]
    _ = μ * μ' * ∑ z, cMat S x z * (1 - (t : ℂ) * (μ * μ'))⁻¹ := by
        congr 1
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.mul_sum, rowSum_neumann hS ht]
    _ = _ := by rw [← Finset.sum_mul, hc1, one_mul, div_eq_mul_inv]

/-- Row sums of the propagator: `Σ_y (P̂_{s,t})_{xy} = (1 - sc)/(1 - tc)`. -/
theorem vsPropagator_rowSum {s t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) (x : Fin N) :
    ∑ y, vsPropagator S μ μ' s t x y =
      (1 - (s : ℂ) * (μ * μ')) / (1 - (t : ℂ) * (μ * μ')) := by
  rw [vsPropagator_eq hS ht]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, vsKernel_rowSum hS ht, Matrix.one_apply, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  have h := one_sub_ne_zero ht
  rw [eq_div_iff h, add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ h]
  ring

/-- `A_t Π = c/(1-tc) Π`. -/
theorem vsKernel_mul_vsPi {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    vsKernel S μ μ' t * vsPi N =
      ((μ * μ') / (1 - (t : ℂ) * (μ * μ'))) • vsPi N := by
  ext x y
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [vsPi]
  rw [← Finset.sum_mul, vsKernel_rowSum hS ht]

/-- `Π A_t = c/(1-tc) Π`. -/
theorem vsPi_mul_vsKernel {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    vsPi N * vsKernel S μ μ' t =
      ((μ * μ') / (1 - (t : ℂ) * (μ * μ'))) • vsPi N := by
  ext x y
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [vsPi]
  simp_rw [vsKernel_symm hS ht _ y]
  rw [← Finset.mul_sum, vsKernel_rowSum hS ht, mul_comm]

/-- For `μ' = conj μ` and `t ≥ 0`, the kernel is real and entrywise nonnegative. -/
theorem vsKernel_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht : ‖(t : ℂ) * (μ * conj μ)‖ < 1)
    (x y : Fin N) :
    (vsKernel S μ (conj μ) t x y).im = 0 ∧ 0 ≤ (vsKernel S μ (conj μ) t x y).re := by
  have hc : μ * conj μ = ((‖μ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  set g : ℕ → ℝ := fun k => ‖μ‖ ^ 2 * ((t * ‖μ‖ ^ 2) ^ k * (S ^ (k + 1)) x y) with hg
  have hfg : ∀ k : ℕ, (μ * conj μ) * (((t : ℂ) * (μ * conj μ)) ^ k *
      ((S ^ (k + 1)) x y : ℂ)) = (g k : ℂ) := fun k => by
    rw [hg, hc]
    push_cast
    ring
  have hsum := (summable_term hS ht 1 x y).mul_left (μ * conj μ)
  simp_rw [hfg] at hsum
  have hgs : Summable g := Complex.summable_ofReal.mp hsum
  have hval : vsKernel S μ (conj μ) t x y = ((∑' k, g k : ℝ) : ℂ) := by
    rw [vsKernel_apply hS ht, ← Summable.tsum_mul_left _ (summable_term hS ht 1 x y)]
    simp_rw [hfg]
    exact (Complex.ofReal_tsum g).symm
  rw [hval, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, tsum_nonneg fun k => ?_⟩
  rw [hg]
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (_root_.pow_nonneg (by positivity) _)
    (hS.pow_nonneg _ x y))

end Identities

/-!
## Time derivatives
-/

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Entry evaluation as a continuous `ℝ`-linear map (local `Matrix.linftyOpNormedRing` norm). -/
def entryCLM (x y : Fin N) : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem commute_vsY_cMat (μ μ' : ℂ) : Commute (vsY S μ μ') (cMat S) :=
  (Commute.refl _).smul_left _

theorem commute_one_sub_vsY_cMat (μ μ' : ℂ) (s : ℝ) :
    Commute (1 - (s : ℂ) • vsY S μ μ') (cMat S) :=
  (Commute.one_left _).sub_left ((commute_vsY_cMat μ μ').smul_left _)

theorem commute_inv_of_commute_cMat (hS : StochasticSymm S) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : Commute M (cMat S)) {μ μ' : ℂ} {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    Commute M (1 - (t : ℂ) • vsY S μ μ')⁻¹ := by
  rw [smul_vsY]
  exact commute_inv_one_sub_smul hS hM ht

/-- Entrywise derivative of the resolvent `R_r = (1 - rY)⁻¹`: `∂_r R_r = R_r Y R_r`. -/
theorem hasDerivAt_inv_entry (hS : StochasticSymm S) {μ μ' : ℂ} {t : ℝ}
    (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) (x y : Fin N) :
    HasDerivAt (fun r : ℝ => (1 - (r : ℂ) • vsY S μ μ')⁻¹ x y)
      (((1 - (t : ℂ) • vsY S μ μ')⁻¹ * vsY S μ μ' * (1 - (t : ℂ) • vsY S μ μ')⁻¹) x y) t := by
  set Y := vsY S μ μ'
  have hdet : IsUnit (1 - (t : ℂ) • Y).det :=
    Matrix.isUnit_det_of_right_inverse (one_sub_vsY_mul_inv hS ht)
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have haff := ((hasDerivAt_id t).smul_const Y).const_sub (1 : Matrix (Fin N) (Fin N) ℂ)
  have hc := hinv.comp_hasDerivAt_of_eq t haff (by rw [hu, id, Complex.coe_smul])
  have hm := (entryCLM x y).hasFDerivAt.comp_hasDerivAt t hc
  refine (hm.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
  · show ((-(ContinuousLinearMap.mulLeftRight ℝ _ (↑u⁻¹ : Matrix (Fin N) (Fin N) ℂ)
      (↑u⁻¹ : Matrix (Fin N) (Fin N) ℂ))) (-((1 : ℝ) • Y))) x y = _
    rw [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, one_smul,
      Matrix.coe_units_inv, hu, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  · show (1 - (r : ℂ) • Y)⁻¹ x y = (Ring.inverse (1 - id r • Y)) x y
    rw [id, Complex.coe_smul, Matrix.nonsing_inv_eq_ringInverse]

/-- **`∂_t A_t = A_t²`**, entrywise. -/
theorem hasDerivAt_vsKernel (hS : StochasticSymm S) {μ μ' : ℂ} {t : ℝ}
    (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) (x y : Fin N) :
    HasDerivAt (fun r : ℝ => vsKernel S μ μ' r x y)
      ((vsKernel S μ μ' t * vsKernel S μ μ' t) x y) t := by
  set Y := vsY S μ μ'
  have h := HasDerivAt.fun_sum (u := Finset.univ) (x := t) fun z _ =>
    (hasDerivAt_inv_entry hS ht z y).const_mul (Y x z)
  have hval : (vsKernel S μ μ' t * vsKernel S μ μ' t) =
      Y * ((1 - (t : ℂ) • Y)⁻¹ * Y * (1 - (t : ℂ) • Y)⁻¹) := by
    unfold vsKernel
    simp only [Matrix.mul_assoc]
    rfl
  rw [hval]
  exact h

/-- **`∂_t P̂_{s,t} = A_t P̂_{s,t}`**, entrywise. -/
theorem hasDerivAt_vsPropagator (hS : StochasticSymm S) {μ μ' : ℂ} (s : ℝ) {t : ℝ}
    (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) (x y : Fin N) :
    HasDerivAt (fun r : ℝ => vsPropagator S μ μ' s r x y)
      ((vsKernel S μ μ' t * vsPropagator S μ μ' s t) x y) t := by
  set Y := vsY S μ μ'
  set B := 1 - (s : ℂ) • Y
  set R := (1 - (t : ℂ) • Y)⁻¹
  have h := HasDerivAt.fun_sum (u := Finset.univ) (x := t) fun z _ =>
    (hasDerivAt_inv_entry hS ht z y).const_mul (B x z)
  have hc1 : Commute Y B := (Commute.one_right Y).sub_right ((Commute.refl Y).smul_right _)
  have hc2 : Commute R B :=
    (commute_inv_of_commute_cMat hS (commute_one_sub_vsY_cMat μ μ' s) ht).symm
  have hY : Commute Y R := commute_inv_of_commute_cMat hS (commute_vsY_cMat μ μ') ht
  have hval : vsKernel S μ μ' t * vsPropagator S μ μ' s t = B * (R * Y * R) := by
    show Y * R * (B * R) = B * (R * Y * R)
    calc Y * R * (B * R) = (R * Y) * (B * R) := by rw [hY.eq]
      _ = R * (Y * B) * R := by simp only [Matrix.mul_assoc]
      _ = R * (B * Y) * R := by rw [hc1.eq]
      _ = (R * B) * (Y * R) := by simp only [Matrix.mul_assoc]
      _ = (B * R) * (Y * R) := by rw [hc2.eq]
      _ = B * (R * Y * R) := by simp only [Matrix.mul_assoc]
  rw [hval]
  exact h

end Deriv

/-!
## Collected statement
-/

/-- `‖t μ μ'‖ < 1` for `|μ|, |μ'| < 1`, `t ∈ [0,1]`. -/
theorem norm_smul_lt_one {μ μ' : ℂ} (hμ : ‖μ‖ < 1) (hμ' : ‖μ'‖ < 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : ‖(t : ℂ) * (μ * μ')‖ < 1 := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  calc t * (‖μ‖ * ‖μ'‖) ≤ ‖μ‖ * ‖μ'‖ :=
        mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ht1
    _ ≤ ‖μ'‖ := mul_le_of_le_one_left (norm_nonneg _) hμ.le
    _ < 1 := hμ'

/-- **Kernel algebra**. For a stochastic symmetric `S`,
`|μ|, |μ'| < 1` and `s, t ∈ [0,1]`, with `c = μμ'`, `A = vsKernel S μ μ'`,
`P̂ = vsPropagator S μ μ'`: Neumann series (entrywise absolutely convergent); `P̂_{s,t} = I +
(t-s)A_t`; `P̂_{s,s} = I`; `A_t = P̂_{s,t} A_s`; `A_t - A_s = (t-s)A_tA_s`; entrywise
`∂_t A_t = A_t²` and `∂_t P̂_{s,t} = A_t P̂_{s,t}`; `A_t` symmetric; `A_t` commutes with `S_ℂ`
and with `A_r(ν,ν')` for `|ν|, |ν'| < 1`, `r ∈ [0,1]`; row sums `c/(1-tc)` and `(1-sc)/(1-tc)`;
`Π A_t = A_t Π = c/(1-tc) Π`; for `μ' = conj μ`, `A_t` is real and `≥ 0` entrywise. -/
theorem vsKernel_algebra {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) {μ μ' : ℂ}
    (hμ : ‖μ‖ < 1) (hμ' : ‖μ'‖ < 1) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    (∀ x y, Summable (fun k : ℕ => ‖((t : ℂ) ^ k • vsY S μ μ' ^ (k + 1)) x y‖) ∧
      HasSum (fun k : ℕ => ((t : ℂ) ^ k • vsY S μ μ' ^ (k + 1)) x y)
        (vsKernel S μ μ' t x y)) ∧
    vsPropagator S μ μ' s t = 1 + ((t : ℂ) - s) • vsKernel S μ μ' t ∧
    vsPropagator S μ μ' s s = 1 ∧
    vsKernel S μ μ' t = vsPropagator S μ μ' s t * vsKernel S μ μ' s ∧
    vsKernel S μ μ' t - vsKernel S μ μ' s =
      ((t : ℂ) - s) • (vsKernel S μ μ' t * vsKernel S μ μ' s) ∧
    (∀ x y, HasDerivAt (fun r : ℝ => vsKernel S μ μ' r x y)
      ((vsKernel S μ μ' t * vsKernel S μ μ' t) x y) t) ∧
    (∀ x y, HasDerivAt (fun r : ℝ => vsPropagator S μ μ' s r x y)
      ((vsKernel S μ μ' t * vsPropagator S μ μ' s t) x y) t) ∧
    (vsKernel S μ μ' t)ᵀ = vsKernel S μ μ' t ∧
    Commute (cMat S) (vsKernel S μ μ' t) ∧
    (∀ (ν ν' : ℂ) (r : ℝ), ‖ν‖ < 1 → ‖ν'‖ < 1 → 0 ≤ r → r ≤ 1 →
      Commute (vsKernel S μ μ' t) (vsKernel S ν ν' r)) ∧
    (∀ x, ∑ y, vsKernel S μ μ' t x y = (μ * μ') / (1 - (t : ℂ) * (μ * μ'))) ∧
    (∀ x, ∑ y, vsPropagator S μ μ' s t x y =
      (1 - (s : ℂ) * (μ * μ')) / (1 - (t : ℂ) * (μ * μ'))) ∧
    vsPi N * vsKernel S μ μ' t = ((μ * μ') / (1 - (t : ℂ) * (μ * μ'))) • vsPi N ∧
    vsKernel S μ μ' t * vsPi N = ((μ * μ') / (1 - (t : ℂ) * (μ * μ'))) • vsPi N ∧
    (μ' = conj μ → ∀ x y,
      (vsKernel S μ μ' t x y).im = 0 ∧ 0 ≤ (vsKernel S μ μ' t x y).re) := by
  have ht := norm_smul_lt_one hμ hμ' ht0 ht1
  have hs := norm_smul_lt_one hμ hμ' hs0 hs1
  refine ⟨fun x y => vsKernel_hasSum hS ht x y, vsPropagator_eq hS ht, vsPropagator_self hS hs,
    vsKernel_eq_propagator_mul hS hs ht, vsKernel_sub hS hs ht,
    fun x y => hasDerivAt_vsKernel hS ht x y, fun x y => hasDerivAt_vsPropagator hS s ht x y,
    vsKernel_transpose hS ht, commute_cMat_vsKernel hS ht, ?_,
    fun x => vsKernel_rowSum hS ht x, fun x => vsPropagator_rowSum hS ht x,
    vsPi_mul_vsKernel hS ht, vsKernel_mul_vsPi hS ht, ?_⟩
  · intro ν ν' r hν hν' hr0 hr1
    have hr := norm_smul_lt_one hν hν' hr0 hr1
    exact (commute_vsKernel_of_commute hS (commute_cMat_vsKernel hS ht).symm hr)
  · rintro rfl x y
    exact vsKernel_nonneg hS ht0 ht x y

/-!
## The saturated kernel `T̂_t = A_t(z, z̄)` for `z` in the bulk
-/

/-- The VS height `η_t = Im z + (1-t) Im m(z)`. -/
def vsHeight (z : ℂ) (t : ℝ) : ℝ := z.im + (1 - t) * (semicircleM z).im

/-- The identity `|m|² η_t = Im m (1 - t|m|²)`, `m = semicircleM z` (every `z`, `t`). -/
theorem vsHeight_identity (z : ℂ) (t : ℝ) :
    ‖semicircleM z‖ ^ 2 * vsHeight z t =
      (semicircleM z).im * (1 - t * ‖semicircleM z‖ ^ 2) := by
  have h := im_identity_of_root (semicircleM_dyson z)
  unfold vsHeight
  linear_combination h

/-- For a stochastic
symmetric `S` on `Fin N`, `N ≥ 1`, `z ∈ 𝒟` (`BulkDomain N δ₀ κ C₀ z`), `μ = m = semicircleM z`,
`μ' = conj m` (so `A_t = T̂_t`, `c = |m|²`), `s, t ∈ [0,1]`, `η_r = vsHeight z r`:
`η_t > 0`;
`T̂_t` is real and `≥ 0` entrywise; sum rule `T̂_t 𝟙 = (Im m/η_t) 𝟙`;
`Π T̂_t = T̂_t Π = (Im m/η_t) Π`, i.e. every entry of `Π T̂_t` is `Im m/(N η_t)`; saturated mode
`P̂_{s,t} 𝟙 = (η_s/η_t) 𝟙`.
(Only `Im z > 0` is used from `z ∈ 𝒟`.)
-/
theorem vsKernel_theta {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) (hN : 0 < N)
    {δ₀ κ C₀ : ℝ} {z : ℂ} (hz : BulkDomain N δ₀ κ C₀ z) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < vsHeight z t ∧
    (∀ x y, (vsKernel S (semicircleM z) (conj (semicircleM z)) t x y).im = 0 ∧
      0 ≤ (vsKernel S (semicircleM z) (conj (semicircleM z)) t x y).re) ∧
    (∀ x, ∑ y, vsKernel S (semicircleM z) (conj (semicircleM z)) t x y =
      (((semicircleM z).im / vsHeight z t : ℝ) : ℂ)) ∧
    vsPi N * vsKernel S (semicircleM z) (conj (semicircleM z)) t =
      (((semicircleM z).im / vsHeight z t : ℝ) : ℂ) • vsPi N ∧
    vsKernel S (semicircleM z) (conj (semicircleM z)) t * vsPi N =
      (((semicircleM z).im / vsHeight z t : ℝ) : ℂ) • vsPi N ∧
    (∀ a b, (vsPi N * vsKernel S (semicircleM z) (conj (semicircleM z)) t) a b =
      (((semicircleM z).im / (N * vsHeight z t) : ℝ) : ℂ)) ∧
    (∀ x, ∑ y, vsPropagator S (semicircleM z) (conj (semicircleM z)) s t x y =
      ((vsHeight z s / vsHeight z t : ℝ) : ℂ)) := by
  have hη := hz.im_pos hN
  set m := semicircleM z with hmdef
  have hm1 : ‖m‖ < 1 := norm_semicircleM_lt_one hη.ne'
  have hy : 0 < m.im := semicircleM_im_pos hη
  have hm0 : 0 < ‖m‖ := norm_pos_iff.mpr (ne_zero_of_root (semicircleM_dyson z))
  have hmc : ‖conj m‖ < 1 := by rwa [Complex.norm_conj]
  have ht := norm_smul_lt_one hm1 hmc ht0 ht1
  have hs := norm_smul_lt_one hm1 hmc hs0 hs1
  have hηt : 0 < vsHeight z t := by
    unfold vsHeight
    nlinarith
  have hc : m * conj m = ((‖m‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  have hn2 : ‖m‖ ^ 2 < 1 := by nlinarith
  have hDt : 0 < 1 - t * ‖m‖ ^ 2 := by nlinarith
  have hDs : 0 < 1 - s * ‖m‖ ^ 2 := by nlinarith
  have hrat : ‖m‖ ^ 2 / (1 - t * ‖m‖ ^ 2) = m.im / vsHeight z t := by
    rw [div_eq_div_iff hDt.ne' hηt.ne']
    linear_combination vsHeight_identity z t
  have hcast : m * conj m / (1 - (t : ℂ) * (m * conj m)) =
      ((m.im / vsHeight z t : ℝ) : ℂ) := by
    rw [hc, ← hrat]
    push_cast
    ring
  have hPi : vsPi N * vsKernel S m (conj m) t =
      ((m.im / vsHeight z t : ℝ) : ℂ) • vsPi N := by
    rw [vsPi_mul_vsKernel hS ht, hcast]
  have hratP : (1 - s * ‖m‖ ^ 2) / (1 - t * ‖m‖ ^ 2) = vsHeight z s / vsHeight z t := by
    rw [div_eq_div_iff hDt.ne' hηt.ne']
    have key : ‖m‖ ^ 2 * ((1 - s * ‖m‖ ^ 2) * vsHeight z t -
        vsHeight z s * (1 - t * ‖m‖ ^ 2)) = 0 := by
      linear_combination (1 - s * ‖m‖ ^ 2) * vsHeight_identity z t -
        (1 - t * ‖m‖ ^ 2) * vsHeight_identity z s
    have := (mul_eq_zero.mp key).resolve_left (by positivity)
    linarith
  refine ⟨hηt, fun x y => vsKernel_nonneg hS ht0 ht x y, fun x => ?_, hPi, ?_,
    fun a b => ?_, fun x => ?_⟩
  · rw [vsKernel_rowSum hS ht x, hcast]
  · rw [vsKernel_mul_vsPi hS ht, hcast]
  · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [hPi, Matrix.smul_apply, smul_eq_mul]
    simp only [vsPi]
    rw [show ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_mul]
    congr 1
    field_simp
  · rw [vsPropagator_rowSum hS ht x, hc, ← hratP]
    push_cast
    ring

end BlockBand.Native.ErdosRiabov.Kernel
