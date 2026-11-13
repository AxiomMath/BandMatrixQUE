module

public import BlockBand.Transmission.LawForced.ShiftLog

/-!
# Trace-Lipschitz bookkeeping and spectral functions of a contraction

* `TrLip A' A c`: `‖Tr K(A' − A)‖ ≤ ‖K‖c` for every `K` (no trace norm needed). Closed
  under sums, real multiples, `1 − ·`, products (`trLip_mul`: constant `‖B'‖c + ‖A‖d`) and
  resolvents (`trLip_inv`: constant `|w|‖R‖‖R'‖c`).
* `cjf hM f = V diag(f(λ_k)) V*` (`V`, `λ` the eigenbasis of `M ⪰ 0`): multiplicative and
  additive in `f`, `cjf id = M`, `Tr cjf f = Σ_k f(λ_k)`, `‖cjf f‖ ≤ sup|f(λ_k)|`, and
  `(1 + wM)⁻¹ = cjf (1+w·)⁻¹` when `1 + wλ_k ≠ 0` (`resM_eq_cjf`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Generator BlockBand.Transmission.SourceMixing
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `‖Tr K(A' − A)‖ ≤ ‖K‖c` for every `K`. -/
def TrLip (A' A : Matrix (Fin W) (Fin W) ℂ) (c : ℝ) : Prop :=
  ∀ K : Matrix (Fin W) (Fin W) ℂ, ‖(K * (A' - A)).trace‖ ≤ ‖K‖ * c

theorem trLip_refl (A : Matrix (Fin W) (Fin W) ℂ) : TrLip A A 0 := fun K => by simp

theorem trLip_mono {A' A : Matrix (Fin W) (Fin W) ℂ} {c d : ℝ} (h : TrLip A' A c) (hcd : c ≤ d) :
    TrLip A' A d := fun K => (h K).trans (mul_le_mul_of_nonneg_left hcd (norm_nonneg _))

theorem trLip_add {A' A B' B : Matrix (Fin W) (Fin W) ℂ} {c d : ℝ} (hA : TrLip A' A c)
    (hB : TrLip B' B d) : TrLip (A' + B') (A + B) (c + d) := fun K => by
  rw [show A' + B' - (A + B) = (A' - A) + (B' - B) by abel, Matrix.mul_add, trace_add, mul_add]
  exact (norm_add_le _ _).trans (add_le_add (hA K) (hB K))

theorem trLip_smul {A' A : Matrix (Fin W) (Fin W) ℂ} {c : ℝ} (hA : TrLip A' A c) (r : ℝ) :
    TrLip ((r : ℂ) • A') ((r : ℂ) • A) (|r| * c) := fun K => by
  rw [← smul_sub, Matrix.mul_smul, trace_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc |r| * ‖(K * (A' - A)).trace‖ ≤ |r| * (‖K‖ * c) :=
        mul_le_mul_of_nonneg_left (hA K) (abs_nonneg r)
    _ = ‖K‖ * (|r| * c) := by ring

theorem trLip_sum {ι : Type*} (s : Finset ι) {A' A : ι → Matrix (Fin W) (Fin W) ℂ}
    {c : ι → ℝ} (h : ∀ i ∈ s, TrLip (A' i) (A i) (c i)) :
    TrLip (∑ i ∈ s, A' i) (∑ i ∈ s, A i) (∑ i ∈ s, c i) := fun K => by
  rw [← Finset.sum_sub_distrib, Matrix.mul_sum, trace_sum, Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => h i hi K)

theorem trLip_one_sub {A' A : Matrix (Fin W) (Fin W) ℂ} {c : ℝ} (hA : TrLip A' A c) :
    TrLip (1 - A') (1 - A) c := fun K => by
  rw [show 1 - A' - (1 - A) = -(A' - A) by abel, Matrix.mul_neg, trace_neg, norm_neg]
  exact hA K

/-- **Products**: `TrLip (A'B') (AB) (‖B'‖c + ‖A‖d)`. -/
theorem trLip_mul {A' A B' B : Matrix (Fin W) (Fin W) ℂ} {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : TrLip A' A c) (hB : TrLip B' B d) : TrLip (A' * B') (A * B) (‖B'‖ * c + ‖A‖ * d) :=
    fun K => by
  have e : K * (A' * B' - A * B) = K * (A' - A) * B' + K * A * (B' - B) := by noncomm_ring
  rw [e, trace_add]
  have e1 : (K * (A' - A) * B').trace = ((B' * K) * (A' - A)).trace := by
    rw [trace_mul_comm, Matrix.mul_assoc]
  rw [e1, Matrix.mul_assoc K A]
  refine (norm_add_le _ _).trans ?_
  have t1 := (hA (B' * K)).trans (mul_le_mul_of_nonneg_right (norm_mul_le B' K) hc)
  have t2 := (hB (K * A)).trans (mul_le_mul_of_nonneg_right (norm_mul_le K A) hd)
  rw [← Matrix.mul_assoc]
  calc ‖((B' * K) * (A' - A)).trace‖ + ‖(K * A * (B' - B)).trace‖
      ≤ ‖B'‖ * ‖K‖ * c + ‖K‖ * ‖A‖ * d := add_le_add t1 t2
    _ = ‖K‖ * (‖B'‖ * c + ‖A‖ * d) := by ring

/-- **Resolvents**: `R' − R = −wR'(T' − T)R` gives `TrLip R' R (|w|‖R‖‖R'‖c)`. -/
theorem trLip_inv {T' T R' R : Matrix (Fin W) (Fin W) ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hT : TrLip T' T c) (w : ℝ)
    (hR : (1 + (w : ℂ) • T) * R = 1) (hR' : R' * (1 + (w : ℂ) • T') = 1) :
    TrLip R' R (|w| * ‖R‖ * ‖R'‖ * c) := fun K => by
  have e : R' - R = -((w : ℂ) • (R' * (T' - T) * R)) := by
    have : R' - R = R' * ((1 + (w : ℂ) • T) - (1 + (w : ℂ) • T')) * R := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hR', Matrix.mul_assoc, hR, Matrix.mul_one,
        Matrix.one_mul]
    rw [this]
    rw [show (1 + (w : ℂ) • T) - (1 + (w : ℂ) • T') = -((w : ℂ) • (T' - T)) by
      rw [smul_sub]; abel]
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : (K * (R' - R)).trace = -((w : ℂ) * ((R * K * R') * (T' - T)).trace) := by
    rw [e, Matrix.mul_neg, trace_neg, Matrix.mul_smul, trace_smul, smul_eq_mul]
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
  rw [e2, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := hT (R * K * R')
  have h2 : ‖R * K * R'‖ ≤ ‖R‖ * ‖K‖ * ‖R'‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  calc |w| * ‖((R * K * R') * (T' - T)).trace‖ ≤ |w| * (‖R * K * R'‖ * c) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg w)
    _ ≤ |w| * ((‖R‖ * ‖K‖ * ‖R'‖) * c) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hc) (abs_nonneg w)
    _ = ‖K‖ * (|w| * ‖R‖ * ‖R'‖ * c) := by ring

/-!
## Spectral functions
-/

variable {M : Matrix (Fin W) (Fin W) ℂ}

/-- `f(M) = V diag(f(λ_k)) V*`. -/
def cjf (hM : M.PosSemidef) (f : ℝ → ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  ts_U hM * diagonal (fun k => ((f (ts_lam hM k) : ℝ) : ℂ)) * star (ts_U hM)

theorem cjf_congr (hM : M.PosSemidef) {f g : ℝ → ℝ} (h : ∀ k, f (ts_lam hM k) = g (ts_lam hM k)) :
    cjf hM f = cjf hM g := by
  unfold cjf
  rw [show (fun k => ((f (ts_lam hM k) : ℝ) : ℂ)) = (fun k => ((g (ts_lam hM k) : ℝ) : ℂ)) from
    funext fun k => by rw [h k]]

theorem cjf_mul (hM : M.PosSemidef) (f g : ℝ → ℝ) :
    cjf hM f * cjf hM g = cjf hM (fun t => f t * g t) := by
  unfold cjf
  have e : ts_U hM * diagonal (fun k => ((f (ts_lam hM k) : ℝ) : ℂ)) * star (ts_U hM) *
      (ts_U hM * diagonal (fun k => ((g (ts_lam hM k) : ℝ) : ℂ)) * star (ts_U hM)) =
      ts_U hM * (diagonal (fun k => ((f (ts_lam hM k) : ℝ) : ℂ)) *
        (star (ts_U hM) * ts_U hM) * diagonal (fun k => ((g (ts_lam hM k) : ℝ) : ℂ))) *
        star (ts_U hM) := by
    simp only [Matrix.mul_assoc]
  rw [e, ts_U_star_mul hM, Matrix.mul_one, diagonal_mul_diagonal]
  congr 2; funext k; push_cast; ring

theorem cjf_add (hM : M.PosSemidef) (f g : ℝ → ℝ) :
    cjf hM f + cjf hM g = cjf hM (fun t => f t + g t) := by
  unfold cjf
  rw [← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
  congr 2; funext k; push_cast; ring

theorem cjf_smul (hM : M.PosSemidef) (r : ℝ) (f : ℝ → ℝ) :
    (r : ℂ) • cjf hM f = cjf hM (fun t => r * f t) := by
  unfold cjf
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
  congr 3; funext k; simp

theorem cjf_sum {ι : Type*} (s : Finset ι) (hM : M.PosSemidef) (f : ι → ℝ → ℝ) :
    ∑ i ∈ s, cjf hM (f i) = cjf hM (fun t => ∑ i ∈ s, f i t) := by
  unfold cjf
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  ext a b
  simp only [Matrix.sum_apply, diagonal_apply]
  split_ifs <;> simp

theorem cjf_id (hM : M.PosSemidef) : cjf hM (fun t => t) = M := (ts_spectral hM).symm

theorem cjf_one (hM : M.PosSemidef) : cjf hM (fun _ => 1) = 1 := by
  unfold cjf
  simp only [Complex.ofReal_one, diagonal_one, Matrix.mul_one, ts_U_mul_star hM]

theorem trace_cjf (hM : M.PosSemidef) (f : ℝ → ℝ) :
    (cjf hM f).trace = ((∑ k, f (ts_lam hM k) : ℝ) : ℂ) := by
  unfold cjf
  rw [trace_mul_comm, ← Matrix.mul_assoc, ts_U_star_mul hM, Matrix.one_mul, trace_diagonal]
  push_cast; rfl

theorem norm_cjf_le (hM : M.PosSemidef) {f : ℝ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hf : ∀ k, |f (ts_lam hM k)| ≤ ρ) : ‖cjf hM f‖ ≤ ρ := by
  unfold cjf
  have h1 : ‖ts_U hM‖ ≤ 1 := norm_unitary_le (ts_U_star_mul hM)
  have h2 : ‖star (ts_U hM)‖ ≤ 1 := norm_unitary_le (by rw [star_star]; exact ts_U_mul_star hM)
  have hd : ‖diagonal (fun k => ((f (ts_lam hM k) : ℝ) : ℂ))‖ ≤ ρ := by
    rw [Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg hρ).2 fun k => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hf k
  set D := diagonal (fun k => ((f (ts_lam hM k) : ℝ) : ℂ))
  have h3 : ‖ts_U hM * D‖ ≤ ρ := (norm_mul_le _ _).trans
    (by nlinarith [norm_nonneg (ts_U hM), norm_nonneg D])
  have h4 := norm_mul_le (ts_U hM * D) (star (ts_U hM))
  nlinarith [norm_nonneg (star (ts_U hM)), norm_nonneg (ts_U hM * D)]

/-- `(1 + wM)⁻¹`. -/
def resM (w : ℝ) (M : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (1 + (w : ℂ) • M)⁻¹

theorem one_add_smul_eq_cjf (hM : M.PosSemidef) (w : ℝ) :
    1 + (w : ℂ) • M = cjf hM (fun t => 1 + w * t) := by
  rw [← cjf_add, ← cjf_one hM, ← cjf_smul, cjf_id]

theorem resM_eq_cjf (hM : M.PosSemidef) {w : ℝ} (hw : ∀ k, 1 + w * ts_lam hM k ≠ 0) :
    resM w M = cjf hM (fun t => (1 + w * t)⁻¹) ∧
      (1 + (w : ℂ) • M) * cjf hM (fun t => (1 + w * t)⁻¹) = 1 ∧
      cjf hM (fun t => (1 + w * t)⁻¹) * (1 + (w : ℂ) • M) = 1 := by
  have hr : (1 + (w : ℂ) • M) * cjf hM (fun t => (1 + w * t)⁻¹) = 1 := by
    rw [one_add_smul_eq_cjf hM w, cjf_mul, ← cjf_one hM]
    exact cjf_congr hM fun k => mul_inv_cancel₀ (hw k)
  have hl : cjf hM (fun t => (1 + w * t)⁻¹) * (1 + (w : ℂ) • M) = 1 := by
    rw [one_add_smul_eq_cjf hM w, cjf_mul, ← cjf_one hM]
    exact cjf_congr hM fun k => inv_mul_cancel₀ (hw k)
  exact ⟨Matrix.inv_eq_right_inv hr, hr, hl⟩

end BlockBand.Transmission.LawForced
