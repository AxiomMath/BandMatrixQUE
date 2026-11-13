module

public import BlockBand.SourceProcess.ClosedSum.Main

/-!
# Start value and closed transport for **admissible** time-`s` frames

`ae_closedGramAt_start` and the closed-transport iterate `ae_closedCurrent_iterate_disc` are
stated for `physCurFrame`, which is not known to be measurable, so `ClosedSummed`/`ClosedTight`
cannot be applied to it. This module proves the deterministic steps for every frame `Vs` in
`IsTimeSFrame`; the almost sure forms `ae_closedGramAt_start_adm` and
`ae_closedCurrent_iterate_adm` are proved from them in the sibling module `StartAE`.

* `one_sub_mul_sq_sub` (projections): `(1−P)(Q−P)² = (1−P)Q(1−P)`.
* `farTrans_mulVec_far`: if `(Q−P)v = c v` with `Q = 𝕊ᴴP𝕊`, `𝕊𝕊ᴴ = 1`, then the far part
  `f = ιᴴv` satisfies `(𝕊₀₁ᴴ𝕊₀₁) f = c² f`.
* **`omitted_mul_timeSFrame`**: a `±√t_k` eigencolumn with `t_k > h²` has far part in the
  `t_k`-eigenspace of `T_far`, killed by `A_- = 1{T_far ≤ h²}`; a column with `t_k ≤ h²` is zero
  (its Gram diagonal entry is `0`). Hence `farEmbed A_- · Vs = 0`.
Cited from `StartAE`:
* **`ae_closedGramAt_start_adm`**: a.s., for every sample with no tag born before `n_s` and every
  phase, `closedGramAt n_s Vs = initialGram`.
* **`ae_closedCurrent_iterate_adm`**: a.s., for all `m` and `‖z‖ ≤ 1`,
  `C_{n_s+m}(z)ᴴ (N_{n_s}⋯)ᴴ Vs = (N^cl_{n_s}⋯)ᴴ Vs`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedReduce

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedSum
open BlockBand.Transmission.Bridge
open scoped ComplexOrder

theorem one_sub_mul_sq_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {P Q : Matrix ι ι ℂ}
    (hP : P * P = P) (hQ : Q * Q = Q) :
    (1 - P) * ((Q - P) * (Q - P)) = (1 - P) * Q * (1 - P) := by
  have e : (1 - P) * ((Q - P) * (Q - P)) - (1 - P) * Q * (1 - P) =
      (Q * Q - Q) + (P * P - P * P * P) - P * (Q * Q) + P * P * Q := by noncomm_ring
  rw [← sub_eq_zero, e, hQ, hP, hP]
  abel

variable {W : ℕ}

theorem farInj_conj_mul_nearPortProj : (farInj W)ᴴ * nearPortProj W = 0 := by
  rw [← nearPortProj_conjTranspose, ← conjTranspose_mul, nearPortProj_mul_farInj,
    conjTranspose_zero]

theorem farEmbed_eq_farInj (X : Matrix (Fin W) (Fin W) ℂ) :
    farEmbed X = farInj W * X * (farInj W)ᴴ := by
  have h : farEmbed X * (1 - nearPortProj W) = farEmbed X := by
    rw [Matrix.mul_sub, farEmbed_mul_nearPortProj, Matrix.mul_one, sub_zero]
  rw [← h, one_sub_nearPortProj, ← Matrix.mul_assoc, farEmbed_mul_farInj]

/-- **The far part of a `(Q−P)`-eigenvector is a `T_far`-eigenvector with the squared
eigenvalue.** -/
theorem farTrans_mulVec_far {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hS : S * Sᴴ = 1)
    {v : Fin 2 × Fin W → ℂ} {c : ℂ}
    (hv : (Sᴴ * nearPortProj W * S - nearPortProj W) *ᵥ v = c • v) :
    ((portBlock S 0 1)ᴴ * portBlock S 0 1) *ᵥ ((farInj W)ᴴ *ᵥ v) =
      (c * c) • ((farInj W)ᴴ *ᵥ v) := by
  set P := nearPortProj W
  set Q := Sᴴ * P * S
  have hP : P * P = P := nearPortProj_mul_self
  have hQ : Q * Q = Q := by
    calc Q * Q = Sᴴ * P * (S * Sᴴ) * P * S := by simp only [Q, Matrix.mul_assoc]
      _ = Q := by rw [hS, Matrix.mul_one, Matrix.mul_assoc Sᴴ P P, hP]
  have h2 : ((Q - P) * (Q - P)) *ᵥ v = (c * c) • v := by
    rw [← mulVec_mulVec, hv, mulVec_smul, hv, smul_smul]
  have hFP : (farInj W)ᴴ * (1 - P) = (farInj W)ᴴ := by
    rw [Matrix.mul_sub, Matrix.mul_one, farInj_conj_mul_nearPortProj, sub_zero]
  have key : (farInj W)ᴴ * Q * farInj W * (farInj W)ᴴ =
      (farInj W)ᴴ * ((1 - P) * ((Q - P) * (Q - P))) := by
    rw [one_sub_mul_sq_sub hP hQ, one_sub_nearPortProj]
    simp only [← Matrix.mul_assoc, farInj_conj_mul_self, Matrix.one_mul]
  rw [← farInj_conj_outProj_farInj S, mulVec_mulVec, key, ← mulVec_mulVec, ← mulVec_mulVec, h2,
    mulVec_smul, mulVec_smul, mulVec_mulVec, hFP]

/-- **`A_-` kills every admissible time-`s` frame** (deterministic form). -/
theorem omitted_mul_timeSFrame {b E s h : ℝ} {K : ℕ} {ω : GrowthPath W}
    (Vs : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (hS : scatteringMatrix b E W (closeLen s W) ω * (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1)
    (hG : gramPair (nearPortProj W) Vs = curGramOf (initialGram K (Fin 0) (physTseq b E s W ω) h))
    (hE : ∀ x k, ((physOutProj b E s W ω - nearPortProj W) * Vs) x k =
      modeEig (physTseq b E s W ω k.1.val) k.2 * Vs x k) :
    farEmbed (omittedProj b E h W (closeLen s W) ω) * Vs = 0 := by
  ext x k
  set v : Fin 2 × Fin W → ℂ := fun y => Vs y k
  set t := physTseq b E s W ω k.1.val
  have hcol : (farEmbed (omittedProj b E h W (closeLen s W) ω) * Vs) x k =
      (farEmbed (omittedProj b E h W (closeLen s W) ω) *ᵥ v) x := by
    simp [mul_apply, mulVec, dotProduct, v]
  rw [hcol, Matrix.zero_apply]
  by_cases ht : h ^ 2 < t
  · have hv : (physOutProj b E s W ω - nearPortProj W) *ᵥ v = modeEig t k.2 • v := by
      funext y
      have := hE y k
      simp only [mul_apply] at this
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, v]
      exact this
    have ht0 : 0 ≤ t := (sq_nonneg h).trans ht.le
    have hcc : modeEig t k.2 * modeEig t k.2 = (t : ℂ) := by
      have : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht0]
      unfold modeEig; split_ifs <;> simp [this]
    have hf := farTrans_mulVec_far hS hv
    rw [hcc, ← farTransmission_eq_of_unitary (mul_eq_one_comm.mp hS)] at hf
    have hA := cfc_mulVec_of_eigen (isHermitian_farTransmission b E W (closeLen s W) ω)
      (omitIndicator h) hf
    have hz : omitIndicator h t = 0 := by simp [omitIndicator, not_le.mpr ht]
    rw [hz, Complex.ofReal_zero, zero_smul] at hA
    rw [farEmbed_eq_farInj, ← mulVec_mulVec, ← mulVec_mulVec]
    unfold omittedProj
    rw [hA, mulVec_zero, Pi.zero_apply]
  · have hk := congrArg (fun G => G.1 k k) hG
    have h0 : star v ⬝ᵥ v = 0 := by
      simp only [gramPair, sourceGram, curGramOf, initialGram, initialFrame, mul_apply,
        conjTranspose_apply, submatrix_apply] at hk
      simp only [dotProduct, Pi.star_apply, v]
      rw [hk]
      refine Finset.sum_eq_zero fun y _ => ?_
      have : ¬ (y.1 = k.1 ∧ h ^ 2 < physTseq b E s W ω k.1.val) := fun hy => ht hy.2
      simp [this]
    rw [dotProduct_star_self_eq_zero.1 h0, mulVec_zero, Pi.zero_apply]

end BlockBand.SourceProcess.ClosedReduce
