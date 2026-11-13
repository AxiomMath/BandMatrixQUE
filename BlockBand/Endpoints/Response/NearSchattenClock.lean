module

public import BlockBand.Endpoints.Response.FractionalTrace
public import BlockBand.Endpoints.Response.EdgeClockMoments
public import BlockBand.Endpoints.Response.NearSchattenScalar
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Clock moments: finite-width eigenvalue sums and limiting clock measures

The clock words `clockWord k = (Q P)^k` are the moments of the near clock `A = nearClock`:
* `ns_wordValue_clockWord`, `ns_trace_QP_pow`: `Tr (QP)^k = Tr A^k` (`k ≥ 1`);
* `ns_trace_pow_re`: `Re Tr A^k = Σ_i λ_i^k` (Hermitian `A`);
* `nsClockSum c A = Σ_i λ_i c(λ_i)` (`= ∫ c dμ_A` for `μ_A = Σ_i λ_i δ_{λ_i}`), and
  `ns_polyMoment_trace`: `Σ_l π_l Re Tr A^{l+1} = Σ_i λ_i π(λ_i)` for a polynomial `π`;
* the same on the limit side (`ns_integral_poly_clockMeasure`):
  `∫ π dμ = Σ_l π_l Re Z_{(QP)^{l+1}}` for a clock measure `μ` (`IsClockMeasure`);
* uniform polynomial approximation on `[0, K]` transfers to both sides with error
  `δ · (total mass)` (`ns_clockSum_sub_poly_le`, `ns_integral_sub_poly_le`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Polynomial Filter Topology Set
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-!
## Clock words are near-clock moments
-/

/-- `Tr (QP)^k` as a word value of the one-source family. -/
theorem ns_wordValue_clockWord (b E : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W)
    (κ : Fin 0 → ℕ) (k : ℕ) :
    wordValue b E κ (fun _ => q) W j ω (clockWord k) =
      ((intervalSource b E W j q ω * nearProjection W) ^ k).trace := by
  unfold wordValue clockWord
  rw [List.map_replicate, List.prod_replicate]
  rfl

/-- The near-port inclusion `ℂ^W → ℂ^{2W}`. -/
def nsNearIncl (W : ℕ) : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  fun x y => if x.1 = 0 ∧ x.2 = y then 1 else 0

theorem ns_nearProjection_eq (W : ℕ) : nearProjection W = nsNearIncl W * (nsNearIncl W)ᴴ := by
  ext ⟨i, x⟩ ⟨i', x'⟩
  simp only [nearProjection, diagonal_apply, mul_apply, conjTranspose_apply, nsNearIncl,
    Prod.mk.injEq]
  by_cases hi : i = 0 <;> by_cases hi' : i' = 0 <;> by_cases hx : x = x' <;>
    simp [hi, hi', hx, Finset.sum_ite_eq, eq_comm]

theorem ns_nearIncl_conj_mul (W : ℕ) : (nsNearIncl W)ᴴ * nsNearIncl W = 1 := by
  ext y y'
  simp [mul_apply, conjTranspose_apply, nsNearIncl, one_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, eq_comm]

theorem ns_portBlock_eq (W : ℕ) (Q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    portBlock Q 0 0 = (nsNearIncl W)ᴴ * Q * nsNearIncl W := by
  ext y y'
  simp [mul_apply, conjTranspose_apply, nsNearIncl, portBlock, Fintype.sum_prod_type,
    Fin.sum_univ_two]

/-- `(Q P)^{k+1} = Q V (VᴴQV)^k Vᴴ`, `P = VVᴴ`. -/
theorem ns_QP_pow_succ (W : ℕ) (Q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (k : ℕ) :
    (Q * nearProjection W) ^ (k + 1) =
      Q * nsNearIncl W * ((nsNearIncl W)ᴴ * Q * nsNearIncl W) ^ k * (nsNearIncl W)ᴴ := by
  induction k with
  | zero => rw [pow_one, pow_zero, Matrix.mul_one, ns_nearProjection_eq, Matrix.mul_assoc]
  | succ k ih =>
    rw [pow_succ, ih, ns_nearProjection_eq, pow_succ]
    simp only [Matrix.mul_assoc]

/-- **`Tr (QP)^k = Tr A^k`** for `k ≥ 1`, `A = portBlock Q 0 0` the near-near block. -/
theorem ns_trace_QP_pow (W : ℕ) (Q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {k : ℕ}
    (hk : 1 ≤ k) : ((Q * nearProjection W) ^ k).trace = ((portBlock Q 0 0) ^ k).trace := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [ns_QP_pow_succ, ns_portBlock_eq, trace_mul_comm, pow_succ']
  simp only [Matrix.mul_assoc]

/-- **Clock words are near-clock moments**: `Tr (QP)^k = Tr A^k`, `A = nearClock`, `k ≥ 1`. -/
theorem ns_wordValue_clockWord_eq (b E : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W)
    (κ : Fin 0 → ℕ) {k : ℕ} (hk : 1 ≤ k) :
    wordValue b E κ (fun _ => q) W j ω (clockWord k) = ((nearClock b E W j q ω) ^ k).trace := by
  rw [ns_wordValue_clockWord, ns_trace_QP_pow W _ hk]
  rfl

/-!
## Eigenvalue sums
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Tr A^k = Σ_i λ_i^k` (Hermitian `A`, spectral theorem). -/
theorem ns_trace_pow (A : Matrix n n ℂ) (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) ^ k := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, diagonal_pow, trace_diagonal]
  rfl

theorem ns_trace_pow_re (A : Matrix n n ℂ) (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace.re = ∑ i, hA.eigenvalues i ^ k := by
  rw [ns_trace_pow A hA, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- `Σ_i λ_i c(λ_i)` over the characteristic roots (`= ∫ c dμ_A`, `μ_A = Σ_i λ_i δ_{λ_i}`). -/
def nsClockSum (c : ℝ → ℝ) (A : Matrix n n ℂ) : ℝ :=
  (A.charpoly.roots.map fun z => z.re * c z.re).sum

theorem ns_clockSum_eq (c : ℝ → ℝ) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    nsClockSum c A = ∑ i, hA.eigenvalues i * c (hA.eigenvalues i) := by
  unfold nsClockSum
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  rfl

theorem ns_clockSum_nonneg {c : ℝ → ℝ} (hc : ∀ x, 0 ≤ x → 0 ≤ c x) {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : 0 ≤ nsClockSum c A := by
  rw [ns_clockSum_eq c hA.isHermitian]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hA.eigenvalues_nonneg i) (hc _ (hA.eigenvalues_nonneg i))

/-- The polynomial moment functional `Σ_{l ≤ m} π_l Re z_l` of a vector of word values
(`z_l = Tr (QP)^{l+1}`). -/
def nsPolyMoment (π : ℝ[X]) (m : ℕ) (z : Fin (m + 1) → ℂ) : ℝ :=
  ∑ l : Fin (m + 1), π.coeff l * (z l).re

theorem ns_continuous_polyMoment (π : ℝ[X]) (m : ℕ) : Continuous (nsPolyMoment π m) :=
  continuous_finsetSum _ fun l _ =>
    continuous_const.mul (Complex.continuous_re.comp (continuous_apply l))

/-- `Σ_l π_l Re Tr A^{l+1} = Σ_i λ_i π(λ_i)` (Hermitian `A`, `deg π ≤ m`). -/
theorem ns_polyMoment_trace {A : Matrix n n ℂ} (hA : A.IsHermitian) (π : ℝ[X]) {m : ℕ}
    (hm : π.natDegree ≤ m) :
    nsPolyMoment π m (fun l => (A ^ ((l : ℕ) + 1)).trace) =
      ∑ i, hA.eigenvalues i * π.eval (hA.eigenvalues i) := by
  unfold nsPolyMoment
  simp_rw [ns_trace_pow_re A hA, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_eq_sum_range' (n := m + 1) (by omega), Finset.mul_sum,
    ← Fin.sum_univ_eq_sum_range (fun l => hA.eigenvalues i * (π.coeff l * hA.eigenvalues i ^ l))]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Polynomial approximation at finite width: if `Tr A ≤ K` (`A ⪰ 0`) and `|π - c| ≤ δ` on
`[0, K]`, then `|Σ_i λ_i c(λ_i) - Σ_i λ_i π(λ_i)| ≤ δ Tr A`. -/
theorem ns_clockSum_sub_poly_le {A : Matrix n n ℂ} (hA : A.PosSemidef) {c : ℝ → ℝ} {π : ℝ[X]}
    {K δ : ℝ} (hK : A.trace.re ≤ K) (happ : ∀ x ∈ Icc 0 K, |π.eval x - c x| ≤ δ) :
    |nsClockSum c A - ∑ i, hA.isHermitian.eigenvalues i * π.eval (hA.isHermitian.eigenvalues i)|
      ≤ δ * A.trace.re := by
  rw [ns_clockSum_eq c hA.isHermitian, ← Finset.sum_sub_distrib,
    trace_re_eq_sum_eigenvalues hA.isHermitian, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h0 := hA.eigenvalues_nonneg i
  have hle : hA.isHermitian.eigenvalues i ≤ K := (eigenvalues_le_trace hA i).trans hK
  rw [← mul_sub, abs_mul, abs_of_nonneg h0, abs_sub_comm, mul_comm]
  exact mul_le_mul_of_nonneg_right (happ _ ⟨h0, hle⟩) h0

/-!
## The limit side: clock measures
-/

section Limit

variable {Ω : Type*} {Z : ClockWord → ℝ → Ω → ℂ} {t : ℝ} {ω : Ω} {μ : Measure ℝ}

theorem ns_clockMeasure_ae_mem (h : IsClockMeasure Z t ω μ) :
    ∀ᵐ x ∂μ, x ∈ Icc 0 (Z (clockWord 1) t ω).re := by
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_union_null h.2.1 h.2.2.1)
  simp only [mem_ofPred_eq, mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr hx

theorem ns_clockMeasure_real_univ (h : IsClockMeasure Z t ω μ) :
    μ.real univ = (Z (clockWord 1) t ω).re := by
  have := h.2.2.2 1 le_rfl
  simpa using this

theorem ns_clockMeasure_integrable (h : IsClockMeasure Z t ω μ) {f : ℝ → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  have := h.1
  have hr : μ.restrict (Icc 0 (Z (clockWord 1) t ω).re) = μ :=
    Measure.restrict_eq_self_of_ae_mem (ns_clockMeasure_ae_mem h)
  rw [← hr]
  exact hf.integrableOn_Icc

/-- `∫ π dμ = Σ_l π_l Re Z_{(QP)^{l+1}}` for a clock measure (`deg π ≤ m`). -/
theorem ns_integral_poly_clockMeasure (h : IsClockMeasure Z t ω μ) (π : ℝ[X]) {m : ℕ}
    (hm : π.natDegree ≤ m) :
    ∫ x, π.eval x ∂μ = nsPolyMoment π m (fun l => Z (clockWord ((l : ℕ) + 1)) t ω) := by
  unfold nsPolyMoment
  simp_rw [Polynomial.eval_eq_sum_range' (n := m + 1) (Nat.lt_succ_of_le hm)]
  rw [integral_finsetSum _ fun l _ =>
    (ns_clockMeasure_integrable h ((continuous_pow l).const_smul (π.coeff l))).congr
      (Eventually.of_forall fun x => by simp [smul_eq_mul])]
  rw [← Fin.sum_univ_eq_sum_range (fun l => ∫ x, π.coeff l * x ^ l ∂μ)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]
  congr 1
  have := h.2.2.2 ((l : ℕ) + 1) (by omega)
  simpa using this

/-- Polynomial approximation on the limit side: if `Re Z_{QP} ≤ K` and `|π - c| ≤ δ` on
`[0, K]`, then `|∫ c dμ - ∫ π dμ| ≤ δ Re Z_{QP}`. -/
theorem ns_integral_sub_poly_le (h : IsClockMeasure Z t ω μ) {c : ℝ → ℝ} (hc : Continuous c)
    {π : ℝ[X]} {K δ : ℝ} (hK : (Z (clockWord 1) t ω).re ≤ K)
    (happ : ∀ x ∈ Icc 0 K, |π.eval x - c x| ≤ δ) :
    |∫ x, c x ∂μ - ∫ x, π.eval x ∂μ| ≤ δ * (Z (clockWord 1) t ω).re := by
  have := h.1
  rw [← integral_sub (ns_clockMeasure_integrable h hc)
    (ns_clockMeasure_integrable h (Polynomial.continuous π)), ← ns_clockMeasure_real_univ h]
  have hb : ∀ᵐ x ∂μ, ‖c x - π.eval x‖ ≤ δ := by
    filter_upwards [ns_clockMeasure_ae_mem h] with x hx
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact happ x ⟨hx.1, hx.2.trans hK⟩
  have := norm_integral_le_of_norm_le_const hb
  rwa [Real.norm_eq_abs] at this

end Limit

end BlockBand.Endpoints
