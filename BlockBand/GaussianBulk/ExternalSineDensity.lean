module

public import Mathlib
public import BlockBand.GaussianBulk.ExternalSineAssembly
public import BlockBand.Adapters.CEH.MDEUniqueness

/-!
# The mean-density clause from the kernel clause

The normalized mean density of points at `E` is `ρ + O(N^{-1/2})`. This follows from the
diagonal `ξ = ζ = 0` of the kernel asymptotic (the gauge cancels there) and the
a priori bound `ρ = Im⟨M⟩/π ≤ (π√t)⁻¹`. The latter is `|m_{F,t}(E)| ≤ t^{-1/2}`, proved
here for the boundary MDE (`IsBoundaryMDE`) of every Hermitian `F` on `ℂ^N`, `N > 0`, `t > 0`,
`E ∈ ℝ`, with `Im⟨M⟩ > 0`: the Ward identity (`Adapters.CEH.ward_identity`) gives
`⟨MM*⟩ = 1/t`, and Cauchy–Schwarz (`Adapters.CEH.norm_trace_mul_sq_le`) gives
`|⟨M⟩|² ≤ ⟨MM*⟩`.

`ExternalSineKernelCore` is `ExternalSineKernel` without the density clause;
`externalSineKernel_of_core` and `externalSine_of_core` reduce `ExternalSine`
to it (plus `PSSS.SourceContract`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open MeasureTheory Set Finset Filter Matrix
open BlockBand.External
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal Topology Matrix.Norms.L2Operator ComplexConjugate

/-- The bound `Im⟨M⟩ ≤ t^{-1/2}` for the boundary MDE (`N > 0`, `t > 0`, Hermitian `F`,
real `E`, `Im⟨M⟩ > 0`). -/
theorem im_normalizedTrace_le_of_boundaryMDE {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) (E : ℝ) (M : Matrix (Fin N) (Fin N) ℂ)
    (h : IsBoundaryMDE t F E M) (hpos : 0 < (CEH.normalizedTrace M).im) :
    (CEH.normalizedTrace M).im ≤ (Real.sqrt t)⁻¹ := by
  obtain ⟨hinv, -⟩ := h
  set w : ℂ := (E : ℂ) + (t : ℂ) * CEH.normalizedTrace M with hw
  have hward := congrArg Matrix.trace
    (Adapters.CEH.ward_identity (N := N) ⟨F, hF⟩ (w := w) (M := M) hinv)
  rw [Matrix.trace_sub, Matrix.trace_conjTranspose, Matrix.trace_smul,
    Adapters.CEH.trace_mul_conjTranspose_self, smul_eq_mul] at hward
  have hT : (M.trace).im = w.im * Adapters.CEH.frobSq M := by
    have := congrArg Complex.im hward
    simp at this
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : CEH.normalizedTrace M = (N : ℂ)⁻¹ * M.trace := rfl
  have hmim : (CEH.normalizedTrace M).im = (N : ℝ)⁻¹ * (M.trace).im := by
    rw [hm, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
  have hwim : w.im = t * (CEH.normalizedTrace M).im := by simp [hw]
  -- `⟨MM*⟩ = 1/t`
  have htrim : 0 < (M.trace).im := by
    have := hpos
    rw [hmim] at this
    exact (pos_iff_pos_of_mul_pos this).mp (by positivity) |> fun h => by
      nlinarith [inv_pos.mpr hNr]
  have hfrob : Adapters.CEH.frobSq M = N / t := by
    rw [hwim, hmim] at hT
    field_simp at hT ⊢
    nlinarith [hT]
  -- Cauchy–Schwarz
  have hcs := Adapters.CEH.norm_trace_mul_sq_le M 1
  rw [Matrix.mul_one] at hcs
  have hone : Adapters.CEH.frobSq (1 : Matrix (Fin N) (Fin N) ℂ) = N := by
    have h1 : ∀ i j : Fin N, ‖(1 : Matrix (Fin N) (Fin N) ℂ) i j‖ ^ 2 =
        if i = j then (1 : ℝ) else 0 := by
      intro i j
      rw [Matrix.one_apply]
      split_ifs <;> simp
    simp only [Adapters.CEH.frobSq, h1, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hone, hfrob] at hcs
  have hle : (CEH.normalizedTrace M).im ^ 2 ≤ 1 / t := by
    have h1 : |(CEH.normalizedTrace M).im| ≤ ‖CEH.normalizedTrace M‖ := Complex.abs_im_le_norm _
    have h2 : ‖CEH.normalizedTrace M‖ = (N : ℝ)⁻¹ * ‖M.trace‖ := by
      rw [hm, norm_mul, norm_inv, Complex.norm_natCast]
    have h3 : (CEH.normalizedTrace M).im ^ 2 ≤ ((N : ℝ)⁻¹ * ‖M.trace‖) ^ 2 := by
      rw [← h2, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h3.trans ?_
    rw [mul_pow]
    calc ((N : ℝ)⁻¹) ^ 2 * ‖M.trace‖ ^ 2 ≤ ((N : ℝ)⁻¹) ^ 2 * (N / t * N) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = 1 / t := by field_simp
  have hsq : (CEH.normalizedTrace M).im ≤ Real.sqrt (1 / t) := Real.le_sqrt_of_sq_le hle
  rwa [Real.sqrt_div' 1 ht.le, Real.sqrt_one, one_div] at hsq

/-- The kernel clause of the external-source sine-kernel theorem alone (the kernel asymptotic with
continuous kernel, factorial-correlation identity and real gauge); `ExternalSineKernel` without
the density clause. Proved as `externalSineKernelCore_holds` (from `Johansson.SourceContract`). -/
def ExternalSineKernelCore : Prop :=
  ∀ (A tLo tHi v ELo EHi L : ℝ), 0 < tLo → tLo ≤ tHi → 0 < v →
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian), ‖F‖ ≤ (N : ℝ) ^ A →
      ∀ (t : ℝ≥0), (t : ℝ) ∈ Icc tLo tHi → ∀ E ∈ Icc ELo EHi,
      ∀ M : Matrix (Fin N) (Fin N) ℂ, IsBoundaryMDE (t : ℝ) F E M →
        v ≤ (CEH.normalizedTrace M).im →
        ∃ (Kern : ℝ → ℝ → ℂ) (h : ℝ → ℝ), Continuous (Function.uncurry Kern) ∧
          (∀ k : ℕ, k ≤ N → deformedFactorialCorrelation N t F hF k =
            volume.withDensity (fun x : Fin k → ℝ =>
              ENNReal.ofReal (Matrix.det (fun i j => Kern (x i) (x j))).re)) ∧
          (∀ ξ ∈ Icc (-L) L, ∀ ζ ∈ Icc (-L) L,
            ‖Complex.exp (-(h ξ : ℂ)) *
                Kern (E + ξ / ((N : ℝ) * ((CEH.normalizedTrace M).im / Real.pi)))
                  (E + ζ / ((N : ℝ) * ((CEH.normalizedTrace M).im / Real.pi))) *
                Complex.exp (h ζ : ℂ) / ((N : ℝ) * ((CEH.normalizedTrace M).im / Real.pi)) -
              (sineKernel ξ ζ : ℂ)‖ ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2))

/-- Clause (b) from clause (a): `ExternalSineKernelCore → ExternalSineKernel`. The constant
becomes `|C| · max 1 ((√tLo)⁻¹/π)` and `N₀` becomes `max N₀ 1`; (a) is used at the radius
`max L 0`. -/
theorem externalSineKernel_of_core (hC : ExternalSineKernelCore) : ExternalSineKernel := by
  intro A tLo tHi v ELo EHi L htLo htle hv
  obtain ⟨C, N₀, hcore⟩ := hC A tLo tHi v ELo EHi (max L 0) htLo htle hv
  set ρmax : ℝ := (Real.sqrt tLo)⁻¹ / Real.pi with hρmax
  refine ⟨|C| * max 1 ρmax, max N₀ 1, ?_⟩
  intro N hN F hF hFn t ht E hE M hM hvM
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN)
  obtain ⟨Kern, h, hKc, hcorr, hasym⟩ := hcore N hN₀ F hF hFn t ht E hE M hM hvM
  have hNpow : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
  have hCC : C * (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ |C| * max 1 ρmax * (N : ℝ) ^ (-(1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right (le_trans (le_abs_self C)
      (le_mul_of_one_le_right (abs_nonneg _) (le_max_left _ _))) hNpow
  have hsub : Icc (-L) L ⊆ Icc (-max L 0) (max L 0) :=
    Icc_subset_Icc (neg_le_neg (le_max_left _ _)) (le_max_left _ _)
  refine ⟨Kern, h, hKc, hcorr, fun ξ hξ ζ hζ => (hasym ξ (hsub hξ) ζ (hsub hζ)).trans hCC, ?_⟩
  -- clause (b)
  have h0mem : (0 : ℝ) ∈ Icc (-max L 0) (max L 0) :=
    ⟨neg_nonpos.mpr (le_max_right _ _), le_max_right _ _⟩
  have h0 := hasym 0 h0mem 0 h0mem
  set ρ : ℝ := (CEH.normalizedTrace M).im / Real.pi with hρ_def
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le htLo ht.1
  have him_pos : 0 < (CEH.normalizedTrace M).im := lt_of_lt_of_le hv hvM
  have hρ : 0 < ρ := div_pos him_pos Real.pi_pos
  have hρle : ρ ≤ ρmax := by
    have h1 := im_normalizedTrace_le_of_boundaryMDE hNpos htpos F hF E M hM him_pos
    have h2 : (Real.sqrt t)⁻¹ ≤ (Real.sqrt tLo)⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr htLo) (Real.sqrt_le_sqrt ht.1)
    exact div_le_div_of_nonneg_right (h1.trans h2) Real.pi_pos.le
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hgauge : Complex.exp (-((h 0 : ℝ) : ℂ)) * Kern E E * Complex.exp ((h 0 : ℝ) : ℂ) =
      Kern E E := by
    rw [mul_comm (Complex.exp _) (Kern E E), mul_assoc, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, mul_one]
  simp only [zero_div, add_zero] at h0
  rw [hgauge] at h0
  have hsine : (sineKernel 0 0 : ℂ) = 1 := by simp [sineKernel]
  rw [hsine] at h0
  have hden : (((N : ℝ) : ℂ) * (((CEH.normalizedTrace M).im : ℂ) / (Real.pi : ℂ))) =
      ((N : ℂ) * (ρ : ℂ)) := by
    rw [hρ_def]
    push_cast
    ring
  have hkey : Kern E E / ((N : ℝ) : ℂ) - ((ρ : ℝ) : ℂ) =
      (ρ : ℂ) * (Kern E E / ((N : ℂ) * (ρ : ℂ)) - 1) := by
    have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
    push_cast
    field_simp
  have h0' : ‖Kern E E / ((N : ℂ) * (ρ : ℂ)) - 1‖ ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2) := by
    convert h0 using 4
    exact hden.symm
  have hb : ‖Kern E E / ((N : ℝ) : ℂ) - ((ρ : ℝ) : ℂ)‖ ≤ ρmax * (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
    rw [hkey, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    exact mul_le_mul hρle h0' (norm_nonneg _) (hρ.le.trans hρle)
  refine hb.trans ?_
  have hCN : 0 ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2) := (norm_nonneg _).trans h0'
  have hρmax0 : 0 ≤ ρmax := hρ.le.trans hρle
  calc ρmax * (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) ≤ max 1 ρmax * (|C| * (N : ℝ) ^ (-(1 : ℝ) / 2)) :=
        mul_le_mul (le_max_right _ _) (mul_le_mul_of_nonneg_right (le_abs_self C) hNpow) hCN
          (le_trans zero_le_one (le_max_left _ _))
    _ = |C| * max 1 ρmax * (N : ℝ) ^ (-(1 : ℝ) / 2) := by ring

/-- `ExternalSine` from the kernel clause alone and `PSSS.SourceContract`. The statement from the
Johansson and PSSS source theorems alone is `externalSine_holds`. -/
theorem externalSine_of_core (source : PSSS.SourceContract.{0}) (hC : ExternalSineKernelCore) :
    ExternalSine :=
  externalSine_of_kernel source (externalSineKernel_of_core hC)

end BlockBand.GaussianBulk
