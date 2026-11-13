module

public import BlockBand.Endpoints.Response.RemoteHigherChainKlein
public import BlockBand.Endpoints.Response.RemoteHigherChainScalar

/-!
# The linear fluctuation of a fresh fractional clock

Part of the remote higher-moment theorem. The first-order term of `Tr(·)^p` at the old clock `A`,
evaluated on the centered fresh matrix `U - EU`:
`ℓ(U) = p Σ_i λ_i^p Re (V*(U - Ū)V)_ii` (`rhc_ell`; `V`, `λ` the eigenbasis of `A`).

* `rhc_ell_eLpNorm` — `‖ℓ‖_{L^q} ≤ p H_p(A) C` from the bilinear fluctuation bound
  `‖u*(U - Ū)v‖_{L^q} ≤ C‖u‖‖v‖` (the form of
  `PassiveSourceMixingContract.oneStepFluctuation`, with `C = C_q W^{-1/2}`), by Minkowski.
* `rhc_integral_ell` — `E ℓ = 0` when `Ū = E U` (integrable entries).
* `rhc_integrable_sandwich_entry` — integrability of the entries of `S U S'`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Matrix
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Layers

variable {W : ℕ}

/-- The linear fluctuation `ℓ(U) = p Σ_i λ_i^p Re (V*(U - Ū)V)_ii` at the old clock `A ⪰ 0`. -/
def rhc_ell (p : ℝ) {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.PosSemidef)
    (U Ub : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  p * ∑ i, hA.isHermitian.eigenvalues i ^ p *
    ((star (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) * (U - Ub) *
      (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)) i i).re

/-- The entries of `S U S'` are integrable when those of `U` are. -/
theorem rhc_integrable_sandwich_entry {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : Ω → Matrix (Fin W) (Fin W) ℂ} (hU : ∀ a c, Integrable (fun ω => U ω a c) μ)
    (S S' : Matrix (Fin W) (Fin W) ℂ) (a c : Fin W) :
    Integrable (fun ω => (S * U ω * S') a c) μ := by
  simp only [Matrix.mul_apply]
  exact integrable_finsetSum _ fun l _ =>
    (integrable_finsetSum _ fun k _ => (hU k l).const_mul _).mul_const _

/-- `ℓ` is continuous in `U`. -/
theorem rhc_continuous_ell (p : ℝ) {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.PosSemidef)
    (Ub : Matrix (Fin W) (Fin W) ℂ) : Continuous fun U => rhc_ell p hA U Ub := by
  unfold rhc_ell
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul ?_)
  refine Complex.continuous_re.comp ?_
  have h : Continuous fun U : Matrix (Fin W) (Fin W) ℂ =>
      star (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) * (U - Ub) *
        (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) :=
    (continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const
  exact (continuous_apply i).comp ((continuous_apply i).comp h)

/-- **Moments of the linear fluctuation** (Minkowski): if every bilinear entry of `U - Ū`
has `L^q` norm at most `C‖u‖‖v‖`, then `‖ℓ(U)‖_{L^q} ≤ p H_p(A) C`. -/
theorem rhc_ell_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ} (hp0 : 0 < p)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.PosSemidef) {U : Ω → Matrix (Fin W) (Fin W) ℂ}
    (hUm : Measurable U) (Ub : Matrix (Fin W) (Fin W) ℂ) {q : ℝ≥0∞} (hq : 1 ≤ q) {C : ℝ}
    (hC : 0 ≤ C)
    (hfl : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (U ω - Ub) v) q μ ≤
      ENNReal.ofReal (C * vecNorm u * vecNorm v)) :
    eLpNorm (fun ω => rhc_ell p hA (U ω) Ub) q μ ≤ ENNReal.ofReal (p * fracTrace p A * C) := by
  set V : Matrix (Fin W) (Fin W) ℂ := (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
  have hV : V ∈ unitaryGroup (Fin W) ℂ := hA.isHermitian.eigenvectorUnitary.2
  set lam := hA.isHermitian.eigenvalues
  have hlam : ∀ i, 0 ≤ lam i ^ p := fun i => Real.rpow_nonneg (hA.eigenvalues_nonneg i) _
  set f : Fin W → Ω → ℝ := fun i ω => (p * lam i ^ p) * ((star V * (U ω - Ub) * V) i i).re
  have hfun : (fun ω => rhc_ell p hA (U ω) Ub) = ∑ i, f i := by
    funext ω
    simp only [rhc_ell, Finset.sum_apply, f, Finset.mul_sum, mul_assoc]
    rfl
  have hbil : ∀ i, (fun ω => (star V * (U ω - Ub) * V) i i) =
      fun ω => bilinear (fun a => V a i) (U ω - Ub) (fun a => V a i) := fun i => by
    funext ω; rw [cej_bilinear_col]
  have hmeas : ∀ i, AEStronglyMeasurable (fun ω => ((star V * (U ω - Ub) * V) i i).re) μ := by
    intro i
    have h : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => ((star V * (M - Ub) * V) i i).re :=
      Complex.continuous_re.comp ((continuous_apply i).comp ((continuous_apply i).comp
        ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul
          continuous_const)))
    exact (h.measurable.comp hUm).aestronglyMeasurable
  have hterm : ∀ i, eLpNorm (f i) q μ ≤ ENNReal.ofReal (p * lam i ^ p * C) := by
    intro i
    have e : f i = (p * lam i ^ p) • fun ω => ((star V * (U ω - Ub) * V) i i).re := by
      funext ω; simp only [f, Pi.smul_apply, smul_eq_mul]
    rw [e, eLpNorm_const_smul]
    have h1 : eLpNorm (fun ω => ((star V * (U ω - Ub) * V) i i).re) q μ ≤
        eLpNorm (fun ω => (star V * (U ω - Ub) * V) i i) q μ :=
      eLpNorm_mono (hmeas i) fun ω => by
        rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
    have h2 := hfl (fun a => V a i) (fun a => V a i)
    rw [cej_vecNorm_col hV i, mul_one, mul_one, ← hbil i] at h2
    have hc : ‖p * lam i ^ p‖ₑ = ENNReal.ofReal (p * lam i ^ p) := by
      rw [Real.enorm_eq_ofReal (by have := hlam i; positivity)]
    calc ‖p * lam i ^ p‖ₑ * eLpNorm (fun ω => ((star V * (U ω - Ub) * V) i i).re) q μ
        ≤ ENNReal.ofReal (p * lam i ^ p) * ENNReal.ofReal C := by
          rw [hc]; gcongr; exact h1.trans h2
      _ = ENNReal.ofReal (p * lam i ^ p * C) :=
          (ENNReal.ofReal_mul (by have := hlam i; positivity)).symm
  rw [hfun]
  refine (eLpNorm_sum_le hq).trans ?_
  calc ∑ i, eLpNorm (f i) q μ ≤ ∑ i, ENNReal.ofReal (p * lam i ^ p * C) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ENNReal.ofReal (∑ i, p * lam i ^ p * C) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => by have := hlam i; positivity).symm
    _ = ENNReal.ofReal (p * fracTrace p A * C) := by
        rw [fracTrace_eq_sum_eigenvalues_of_posSemidef hA p, Finset.mul_sum, Finset.sum_mul]

/-- **The linear fluctuation has mean zero**: `E ℓ(U) = 0` for `Ū = E U` (integrable entries). -/
theorem rhc_integral_ell {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (p : ℝ) {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.PosSemidef) {U : Ω → Matrix (Fin W) (Fin W) ℂ}
    (hU : ∀ a c, Integrable (fun ω => U ω a c) μ) :
    ∫ ω, rhc_ell p hA (U ω) (matrixExpect μ U) ∂μ = 0 := by
  unfold rhc_ell
  set V : Matrix (Fin W) (Fin W) ℂ := (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
  set Ub := matrixExpect μ U
  have hint : ∀ i, Integrable (fun ω => (star V * U ω * V) i i) μ := fun i =>
    rhc_integrable_sandwich_entry hU _ _ i i
  have hmean : ∀ i, ∫ ω, (star V * U ω * V) i i ∂μ = (star V * Ub * V) i i := fun i => by
    have := congrFun (congrFun (cej_matrixExpect_sandwich hU (star V) V) i) i
    rw [show matrixExpect μ (fun ω => star V * U ω * V) i i = ∫ ω, (star V * U ω * V) i i ∂μ
      from rfl] at this
    exact this
  have hsplit : ∀ ω i, (star V * (U ω - Ub) * V) i i =
      (star V * U ω * V) i i - (star V * Ub * V) i i := fun ω i => by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
  have hzero : ∀ i, ∫ ω, ((star V * (U ω - Ub) * V) i i).re ∂μ = 0 := by
    intro i
    simp_rw [hsplit]
    have hI : Integrable (fun ω => (star V * U ω * V) i i - (star V * Ub * V) i i) μ :=
      (hint i).sub (integrable_const _)
    rw [show (fun ω => ((star V * U ω * V) i i - (star V * Ub * V) i i).re) =
        fun ω => RCLike.re ((star V * U ω * V) i i - (star V * Ub * V) i i) from rfl,
      integral_re hI, integral_sub (hint i) (integrable_const _), hmean i, integral_const]
    simp
  have hint' : ∀ i, Integrable (fun ω => ((star V * (U ω - Ub) * V) i i).re) μ := fun i => by
    have : Integrable (fun ω => (star V * (U ω - Ub) * V) i i) μ := by
      simp_rw [hsplit]; exact (hint i).sub (integrable_const _)
    exact this.re
  rw [integral_const_mul, integral_finsetSum _ fun i _ => (hint' i).const_mul _]
  simp only [integral_const_mul, hzero, mul_zero, Finset.sum_const_zero]

end BlockBand.Endpoints
