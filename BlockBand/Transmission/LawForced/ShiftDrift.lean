module

public import BlockBand.Transmission.LawForced.ShiftLip

/-!
# The `κ ≡ 0` ratio drift: the sum `dsum` in matrix form

By `ratioDrift_traceMeasure`, `ratioDrift D₀ E 0 u z μ_T = F·(D₀/2)·dsum z T` with
`dsum z T = Σx(1+x)S_T(x)² + Σy(1−y)S_T(−y)² + Σ_k t_k²(1−t_k)Λ_z(t_k)²`. In matrix form
`S_T(w) = Re Tr(T(1+wT)⁻¹)` and the last sum is `Re Tr(T·T·(1−T)·Λ(T)·Λ(T))`,
`Λ(T) = Σx_i(1+x_iT)⁻¹ + Σy_j(1−y_jT)⁻¹` (`cjf`). This module defines `dsum` and the constants
`dsK`, `dsB`, and gives these matrix forms (`eigS_eq_trace`, `lamM_eq_cjf`, `third_eq_trace`).

With `TrLip T' T c`, the sibling modules prove:
* **`abs_dsum_sub_le`**: `|dsum z T' − dsum z T| ≤ dsK z·c·(g + g' + 1)`;
* **`dsum_nonneg_le`**: `0 ≤ dsum z T ≤ dsB z·(g + 1)²`;
* **`ratioDrift_shift_le`**: `|ratioDrift(μ_{T'}) − ratioDrift(μ_T)| ≤
  |D₀|/2·(ℓ·dsB(g'+1)² + dsK·c·(g+g'+1))` when `|log F(T') − log F(T)| ≤ ℓ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {p W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ}

/-- The bracket of `ratioDrift_traceMeasure`. -/
def dsum (z : DualCoord p) (hT : T.PosSemidef) : ℝ :=
  (∑ i, z.1 i * (1 + z.1 i) * eigS hT.1 (z.1 i) ^ 2) +
    (∑ j, z.2 j * (1 - z.2 j) * eigS hT.1 (-z.2 j) ^ 2) +
    ∑ k, hT.1.eigenvalues k ^ 2 * (1 - hT.1.eigenvalues k) * dualLam z (hT.1.eigenvalues k) ^ 2

/-- `ρ_y = (1 − y)⁻¹`. -/
def rhoY (y : ℝ) : ℝ := (1 - y)⁻¹

/-- `Σx_i² + Σy_j²ρ_{y_j}²`. -/
def lamLip2 (z : DualCoord p) : ℝ := ∑ i, z.1 i ^ 2 + ∑ j, z.2 j ^ 2 * rhoY (z.2 j) ^ 2

/-- The Lipschitz constant of `dsum`. -/
def dsK (z : DualCoord p) : ℝ :=
  (∑ i, z.1 i * (1 + z.1 i) * (1 + z.1 i)) +
    (∑ j, z.2 j * (1 - z.2 j) * (rhoY (z.2 j) + z.2 j * rhoY (z.2 j) ^ 2) * rhoY (z.2 j)) +
    (3 * lamHat z ^ 2 + 2 * lamHat z * lamLip2 z)

/-- The size constant of `dsum`. -/
def dsB (z : DualCoord p) : ℝ :=
  (∑ i, z.1 i * (1 + z.1 i)) + (∑ j, z.2 j * (1 - z.2 j) * rhoY (z.2 j) ^ 2) + lamHat z ^ 2

section Facts

variable {z : DualCoord p} (hz : IsRatioRange z.1 z.2)
include hz

theorem rhoY_pos (j : Fin p) : 0 < rhoY (z.2 j) := inv_pos.2 (by linarith [(hz.2 j).2])

theorem lamLip2_nonneg : 0 ≤ lamLip2 z :=
  add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.sum_nonneg fun j _ => by
    have := rhoY_pos hz j; positivity)

theorem dsK_nonneg : 0 ≤ dsK z := by
  unfold dsK
  have h1 : 0 ≤ ∑ i, z.1 i * (1 + z.1 i) * (1 + z.1 i) :=
    Finset.sum_nonneg fun i _ => by have := hz.1 i; positivity
  have h2 : 0 ≤ ∑ j, z.2 j * (1 - z.2 j) * (rhoY (z.2 j) + z.2 j * rhoY (z.2 j) ^ 2) *
      rhoY (z.2 j) := Finset.sum_nonneg fun j _ => by
    have := (hz.2 j).1; have := rhoY_pos hz j
    have : 0 ≤ 1 - z.2 j := by linarith [(hz.2 j).2]
    positivity
  have := lamHat_nonneg hz; have := lamLip2_nonneg hz
  positivity

theorem dsB_nonneg : 0 ≤ dsB z := by
  unfold dsB
  have h1 : 0 ≤ ∑ i, z.1 i * (1 + z.1 i) := Finset.sum_nonneg fun i _ => by
    have := hz.1 i; positivity
  have h2 : 0 ≤ ∑ j, z.2 j * (1 - z.2 j) * rhoY (z.2 j) ^ 2 := Finset.sum_nonneg fun j _ => by
    have := (hz.2 j).1; have : 0 ≤ 1 - z.2 j := by linarith [(hz.2 j).2]
    positivity
  positivity

end Facts

/-!
## Matrix forms
-/

section Matrix

variable {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (hT : T.PosSemidef)
  (hT1 : (1 - T).PosSemidef)
include hz hT hT1

theorem one_add_pos_x (i : Fin p) (k : Fin W) : 0 < 1 + z.1 i * ts_lam hT k :=
  pos_x (hz.1 i) (eigenvalues_mem hT hT1 k).1

theorem one_add_pos_y (j : Fin p) (k : Fin W) : 0 < 1 + -z.2 j * ts_lam hT k :=
  pos_y (hz.2 j).2 (hz.2 j).1 (eigenvalues_mem hT hT1 k).2

omit hz hT1 in
/-- `S_T(w) = Re Tr(T(1+wT)⁻¹)`. -/
theorem eigS_eq_trace {w : ℝ} (hw : ∀ k, 0 < 1 + w * ts_lam hT k) :
    eigS hT.1 w = (T * resM w T).trace.re := by
  have h := resM_eq_cjf hT (w := w) fun k => (hw k).ne'
  have e : T * resM w T = cjf hT (fun t => t * (1 + w * t)⁻¹) := by
    have := cjf_mul hT (fun t => t) (fun t => (1 + w * t)⁻¹)
    rw [cjf_id, ← h.1] at this; exact this
  rw [e, trace_cjf, Complex.ofReal_re, eigS]
  exact Finset.sum_congr rfl fun k _ => div_eq_mul_inv _ _

/-- `Λ(T) = Σx_i(1+x_iT)⁻¹ + Σy_j(1−y_jT)⁻¹ = cjf Λ_z`. -/
def lamM (z : DualCoord p) (M : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  ∑ i, (z.1 i : ℂ) • resM (z.1 i) M + ∑ j, (z.2 j : ℂ) • resM (-z.2 j) M

omit hz hT hT1 in
theorem lamM_def (z : DualCoord p) (M : Matrix (Fin W) (Fin W) ℂ) :
    lamM z M = ∑ i, (z.1 i : ℂ) • resM (z.1 i) M + ∑ j, (z.2 j : ℂ) • resM (-z.2 j) M := rfl

theorem lamM_eq_cjf : lamM z T = cjf hT (dualLam z) := by
  have hx : ∀ i, (z.1 i : ℂ) • resM (z.1 i) T = cjf hT (fun t => z.1 i * (1 + z.1 i * t)⁻¹) :=
    fun i => by
      rw [(resM_eq_cjf hT fun k => (one_add_pos_x hz hT hT1 i k).ne').1, cjf_smul]
  have hy : ∀ j, (z.2 j : ℂ) • resM (-z.2 j) T =
      cjf hT (fun t => z.2 j * (1 + -z.2 j * t)⁻¹) := fun j => by
    rw [(resM_eq_cjf hT fun k => (one_add_pos_y hz hT hT1 j k).ne').1, cjf_smul]
  rw [lamM_def]
  simp only [hx, hy]
  rw [cjf_sum, cjf_sum, cjf_add]
  refine cjf_congr hT fun k => ?_
  unfold dualLam
  simp only [div_eq_mul_inv, neg_mul, ← sub_eq_add_neg]

/-- The third sum of `dsum` as a trace. -/
theorem third_eq_trace :
    ∑ k, hT.1.eigenvalues k ^ 2 * (1 - hT.1.eigenvalues k) * dualLam z (hT.1.eigenvalues k) ^ 2 =
      (T * T * (1 - T) * lamM z T * lamM z T).trace.re := by
  have e1 : 1 - T = cjf hT (fun t => 1 - t) := by
    have h := cjf_add hT (fun _ => (1 : ℝ)) (fun t => (-1) * t)
    have h2 := cjf_smul hT (-1) (fun t => t)
    beta_reduce at h h2
    rw [cjf_one, ← h2, cjf_id] at h
    rw [show (fun t : ℝ => 1 - t) = (fun t => 1 + -1 * t) from funext fun t => by ring, ← h]
    push_cast; rw [neg_one_smul, sub_eq_add_neg]
  have hTT : T * T = cjf hT (fun t => t * t) := by
    have := cjf_mul hT (fun t => t) (fun t => t); rwa [cjf_id] at this
  have e : T * T * (1 - T) * lamM z T * lamM z T =
      cjf hT (fun t => t * t * (1 - t) * dualLam z t * dualLam z t) := by
    rw [lamM_eq_cjf hz hT hT1, e1, hTT, cjf_mul, cjf_mul, cjf_mul]
  rw [e, trace_cjf, Complex.ofReal_re]
  exact Finset.sum_congr rfl fun k _ => by simp only [ts_lam]; ring

end Matrix

end BlockBand.Transmission.LawForced
