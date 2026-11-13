module

public import BlockBand.Endpoints.Clock.ClockMixingStep

/-!
# The deterministic-clock lemma: the two covariance identities

The two covariance identities follow by diagonalizing `A` and summing the four-vector identities;
the error sums to `(Tr A)²`, without a dimension factor.

Setting: one fresh one-port layer `ω ~ freshLaw W b` at a deterministic Hermitian old self-energy
`X` (conditioning on the past), `U = LL* = freshU b E X`, `U⁰ = U - E U = freshU0 b E X`,
`f = passiveF b E X`, a deterministic `A ⪰ 0` (in the proof of the lemma `A = A_a(Q)` is
past-measurable), `D₀ = transportD0 b E`, `σ₋ = sigmaMinus b E s` at a stationary jet `s`,
`δ₀ = jetDistance0 b E X`, `δ₁ = jetDistance1 b E s X`.

## Results (fixed `0 < b < 1/2`, `-2 < E < 2`, stationary jet `s`; constants `C, W₀`)

`covIdentities_of`: for `W ≥ W₀`, Hermitian `X`, `A ⪰ 0`, with
`ε = C (W⁻² + W⁻¹(δ₀ + δ₁))`:
* `|E Tr(AU⁰AU⁰) - (D₀/W)(Tr A)² - (σ₋/W)(Tr Af)² - (σ̄₋/W)(Tr Af*)²| ≤ ε (Tr A)²`;
* `|E (Tr AU⁰)² - (D₀/W) Tr A² - (σ₋/W) Tr(AfAf) - (σ̄₋/W) Tr(Af*Af*)| ≤ ε (Tr A)²`.

The two conjuncts of `covTraceSquare_of` are the forms
`E Tr(AU⁰AU⁰) = (D₀/W)(Tr A)² + O(|Tr(Af)|²/W + [(δ₀+δ₁)/W + W⁻²](Tr A)²)` and
`E (Tr AU⁰)² = (D₀/W) Tr A² + O(Tr(AfAf*)/W + [(δ₀+δ₁)/W + W⁻²](Tr A)²)`, using
`|Tr(Af*)| = |Tr(Af)|` and `|Tr(AfAf)|, |Tr(Af*Af*)| ≤ Tr(AfAf*)` for `A ⪰ 0`.

The error carries `δ₁/W` as well as `δ₀/W`, as in the remainder `C[W⁻² + W⁻¹(δ₀ + δ₁ + q/W)]` of
`PassiveCovarianceContract` (with `q = 0` here). Both are `O_{L^p}(W⁻¹)` along the one-ended path
(`OpenInputsMoments`). The hypotheses are `PassiveCovarianceContract` and
`PassiveSourceMixingContract.oneStepFluctuation` at `p = 2` (only for the integrability of the
products of centered entries). On the one-ended path `X` is Hermitian, so `Y = -Im X = 0`,
`T = 4ηR*YR = 0` and `q = 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexConjugate Matrix Matrix.Norms.L2Operator ComplexOrder

/-- The centered transport `U⁰ = U - E(U | X)` of one fresh layer, `U = LL*`
(the deterministic-clock lemma). -/
def freshU0 {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    Matrix (Fin W) (Fin W) ℂ :=
  freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X)

namespace DetClockCov

open ClockMixingAlg

/-!
## 1. Algebra in the eigenbasis of `A`
-/

section Alg

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- `Tr(A M A N) = Σ_{ik} α_i α_k (U*MU)_{ik} (U*NU)_{ki}`. -/
theorem trace_sandwich_two (hA : A.IsHermitian) (M N : Matrix n n ℂ) :
    (A * M * A * N).trace = ∑ i, ∑ k, (hA.eigenvalues i : ℂ) * (hA.eigenvalues k : ℂ) *
      (rot hA M i k * rot hA N k i) := by
  set D : Matrix n n ℂ := diagonal (fun i => (hA.eigenvalues i : ℂ)) with hD
  have key : A * M * A * N = eU hA * (D * rot hA M * D * rot hA N) * star (eU hA) := by
    unfold rot
    conv_lhs => rw [spec hA]
    calc eU hA * D * star (eU hA) * M * (eU hA * D * star (eU hA)) * N
        = eU hA * D * (star (eU hA) * M * eU hA) * D * (star (eU hA) * N) := by
          simp only [Matrix.mul_assoc]
      _ = eU hA * D * (star (eU hA) * M * eU hA) * D *
            (star (eU hA) * N * (eU hA * star (eU hA))) := by
          rw [eU_mul_star hA, Matrix.mul_one]
      _ = eU hA * (D * (star (eU hA) * M * eU hA) * D * (star (eU hA) * N * eU hA)) *
            star (eU hA) := by
          simp only [Matrix.mul_assoc]
  rw [key, trace_mul_comm, ← Matrix.mul_assoc, eU_star_mul hA, Matrix.one_mul]
  rw [trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hD, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

theorem rot_one (hA : A.IsHermitian) : rot hA 1 = 1 := by
  unfold rot; rw [Matrix.mul_one, eU_star_mul hA]

theorem trace_eq_sum (hA : A.IsHermitian) : A.trace = ∑ i, (hA.eigenvalues i : ℂ) := by
  have h := trace_mul_eq_sum hA 1
  rw [Matrix.mul_one, rot_one] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem trace_mul_self_eq_sum (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, (hA.eigenvalues i : ℂ) * (hA.eigenvalues i : ℂ) := by
  have h := trace_sandwich_two hA 1 1
  rw [Matrix.mul_one, Matrix.mul_one, rot_one] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Matrix.one_apply_ne (Ne.symm hk)]
  · simp

end Alg

/-!
## 2. The one-ended (Hermitian) input: `T = 0`, `q = 0`
-/

theorem passiveTransmission_eq_zero {W : ℕ} (b E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) : passiveTransmission b E X = 0 := by
  unfold passiveTransmission passiveQ
  rw [passiveY_eq_zero hX, Matrix.mul_zero, Matrix.zero_mul, smul_zero]

theorem measurable_freshU {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (fun ω : OneEndedLayer W => freshU b E X ω) := by
  have hL : Measurable (fun ω : OneEndedLayer W => freshL b E X ω) :=
    (ClockMixingProb.meas_freshL (W := W) b E).comp (f := fun ω => (X, ω))
      (measurable_const.prodMk measurable_id)
  exact ClockMixingProb.meas_mul hL (ClockMixingProb.meas_conjTranspose hL)

theorem measurable_bilinear {W : ℕ} (u v : Fin W → ℂ) :
    Measurable (fun M : Matrix (Fin W) (Fin W) ℂ => bilinear u M v) := by
  unfold bilinear
  refine Continuous.measurable ?_
  unfold dotProduct mulVec dotProduct
  fun_prop

/-- Centered bilinear entries of `U` are in `L²` (`oneStepFluctuation`, `p = 2`). -/
theorem memLp_bilinear_freshU0 {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) {C : ℝ}
    (hfl : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (freshU b E X ω -
      matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal 2) (freshLaw W b) ≤
        ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v))
    (u v : Fin W → ℂ) :
    MemLp (fun ω => bilinear u (freshU0 b E X ω) v) 2 (freshLaw W b) := by
  have h := hfl u v
  rw [show ENNReal.ofReal 2 = 2 by simp] at h
  exact lt_of_le_of_lt h ENNReal.ofReal_lt_top

/-!
## 3. The covariance identities
-/

/-- **The covariance trace-square and square-trace identities with explicit same-sign terms**, from
`PassiveCovarianceContract` by diagonalizing `A`. -/
theorem covIdentities_of (hcov : PassiveCovarianceContract)
    (hmix : PassiveSourceMixingContract) {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hE0 : -2 < E) (hE1 : E < 2) {s : ℂ} (hs : IsStationaryJet b E s) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ A : Matrix (Fin W) (Fin W) ℂ, A.PosSemidef →
        ‖(∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂freshLaw W b) -
            (((transportD0 b E / W : ℝ)) : ℂ) * A.trace ^ 2 -
            sigmaMinus b E s / W * (A * passiveF b E X).trace ^ 2 -
            conj (sigmaMinus b E s) / W * (A * (passiveF b E X)ᴴ).trace ^ 2‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X)) *
            A.trace.re ^ 2 ∧
        ‖(∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b) -
            (((transportD0 b E / W : ℝ)) : ℂ) * (A * A).trace -
            sigmaMinus b E s / W * (A * passiveF b E X * A * passiveF b E X).trace -
            conj (sigmaMinus b E s) / W *
              (A * (passiveF b E X)ᴴ * A * (passiveF b E X)ᴴ).trace‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X)) *
            A.trace.re ^ 2 := by
  obtain ⟨-, hall⟩ := hcov b hb0 hb1 E hE0 hE1
  obtain ⟨C, W₀, hC⟩ := hall s hs
  obtain ⟨Cf, Wf, hfl⟩ := hmix.oneStepFluctuation b hb0 hb1 E hE0 hE1 2 (by norm_num)
  refine ⟨C, max (max W₀ Wf) 1, fun W hWW X hX A hA => ?_⟩
  have hW0 : W₀ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hWW
  have hWf : Wf ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hWW
  have hWpos : 0 < W := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hWW)
  have hWne : (W : ℂ) ≠ 0 := by exact_mod_cast hWpos.ne'
  set μ := freshLaw W b with hμ
  set f := passiveF b E X with hf
  set D₀ := transportD0 b E with hD₀
  set σ := sigmaMinus b E s with hσ
  set ε := C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X))
    with hε
  set v : Fin W → Fin W → ℂ := fun i a => eU hA.1 a i with hv
  have hα0 : ∀ i, 0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg
  have hvn : ∀ i, vecNorm (v i) = 1 := fun i => vecNorm_eU_col hA.1 i
  have h4 : ∀ i k l m, fourNorm (v i) (v k) (v l) (v m) = 1 := fun i k l m => by
    unfold fourNorm; rw [hvn, hvn, hvn, hvn]; ring
  have hfl2 := fun u w => (hfl W hWf X (passiveY_posSemidef hX) u w).1
  have hmem := memLp_bilinear_freshU0 b E X hfl2
  -- the contract at Hermitian `X`
  have hT := passiveTransmission_eq_zero b E hX
  have hq := passiveMass_eq_zero b E hX
  have hcon : ∀ i k l m, ‖bilinearCovariance μ (freshU b E X) (v i) (v k) (v l) (v m) -
      ((((D₀ / (2 * W) : ℝ)) : ℂ) * (crossedTensor (v i) (v k) (v l) (v m) 1 1 +
          crossedTensor (v i) (v k) (v l) (v m) 1 1) +
        σ / W * crossedTensor (v i) (v k) (v l) (v m) f f +
        conj σ / W * crossedTensor (v i) (v k) (v l) (v m) fᴴ fᴴ)‖ ≤ ε := by
    intro i k l m
    have h := hC W hW0 X (passiveY_posSemidef hX) (v i) (v k) (v l) (v m)
    simp only [hT, sub_zero, hq, zero_div, add_zero, h4, mul_one] at h
    exact h
  have hbil : ∀ (M : Matrix (Fin W) (Fin W) ℂ) i k, bilinear (v i) M (v k) = rot hA.1 M i k :=
    fun M i k => (rot_apply hA.1 M i k).symm
  have hcovint : ∀ i k l m, bilinearCovariance μ (freshU b E X) (v i) (v k) (v l) (v m) =
      ∫ ω, rot hA.1 (freshU0 b E X ω) i k * rot hA.1 (freshU0 b E X ω) l m ∂μ := by
    intro i k l m
    unfold bilinearCovariance
    simp only [← hbil]
    rfl
  have hint : ∀ i k l m, Integrable (fun ω =>
      rot hA.1 (freshU0 b E X ω) i k * rot hA.1 (freshU0 b E X ω) l m) μ := by
    intro i k l m
    have h1 := hmem (v i) (v k)
    have h2 := hmem (v l) (v m)
    simp only [hbil] at h1 h2
    exact h1.integrable_mul h2
  have hTrA : A.trace = ∑ i, (hA.1.eigenvalues i : ℂ) := trace_eq_sum hA.1
  have hTrAre : A.trace.re = ∑ i, hA.1.eigenvalues i := by rw [hTrA, Complex.re_sum]; simp
  -- the error sums to `(Tr A)²`
  have herr : ∀ (c : Fin W → Fin W → ℂ), (∀ i k, ‖c i k‖ ≤ ε) →
      ‖∑ i, ∑ k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) * c i k‖ ≤ ε * A.trace.re ^ 2 := by
    intro c hc
    rw [hTrAre, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hα0 i),
      Real.norm_of_nonneg (hα0 k)]
    have := mul_le_mul_of_nonneg_left (hc i k) (mul_nonneg (hα0 i) (hα0 k))
    linarith
  have hrot1 : ∀ i k, rot hA.1 (1 : Matrix (Fin W) (Fin W) ℂ) i k = if i = k then 1 else 0 :=
    fun i k => by rw [rot_one, Matrix.one_apply]
  have hWr : ((W : ℝ) : ℂ) = (W : ℂ) := by push_cast; rfl
  constructor
  · -- `E Tr(AU⁰AU⁰)`
    have hexp : (∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂μ) =
        ∑ i, ∑ k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          bilinearCovariance μ (freshU b E X) (v i) (v k) (v k) (v i) := by
      simp only [trace_sandwich_two hA.1, hcovint]
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        (hint i k k i).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun k _ => (hint i k k i).const_mul _]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul]
    have hmain : (((D₀ / W : ℝ)) : ℂ) * A.trace ^ 2 + σ / W * (A * f).trace ^ 2 +
        conj σ / W * (A * fᴴ).trace ^ 2 =
        ∑ i, ∑ k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          ((((D₀ / (2 * W) : ℝ)) : ℂ) * (crossedTensor (v i) (v k) (v k) (v i) 1 1 +
            crossedTensor (v i) (v k) (v k) (v i) 1 1) +
          σ / W * crossedTensor (v i) (v k) (v k) (v i) f f +
          conj σ / W * crossedTensor (v i) (v k) (v k) (v i) fᴴ fᴴ) := by
      simp only [crossedTensor, hbil, hrot1, ite_true]
      rw [hTrA, trace_mul_eq_sum hA.1 f, trace_mul_eq_sum hA.1 fᴴ]
      have hterm : ∀ i k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          ((((D₀ / (2 * W) : ℝ)) : ℂ) * (1 * 1 + 1 * 1) +
            σ / W * (rot hA.1 f i i * rot hA.1 f k k) +
            conj σ / W * (rot hA.1 fᴴ i i * rot hA.1 fᴴ k k)) =
          (((D₀ / W : ℝ)) : ℂ) * ((hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ)) +
            σ / W * (((hA.1.eigenvalues i : ℂ) * rot hA.1 f i i) * ((hA.1.eigenvalues k : ℂ) * rot hA.1 f k k)) +
            conj σ / W * (((hA.1.eigenvalues i : ℂ) * rot hA.1 fᴴ i i) * ((hA.1.eigenvalues k : ℂ) * rot hA.1 fᴴ k k)) := by
        intro i k
        push_cast
        field_simp
        ring
      simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sq]

    rw [show (∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂μ) -
        (((D₀ / W : ℝ)) : ℂ) * A.trace ^ 2 - σ / W * (A * f).trace ^ 2 -
        conj σ / W * (A * fᴴ).trace ^ 2 =
        (∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂μ) -
          ((((D₀ / W : ℝ)) : ℂ) * A.trace ^ 2 + σ / W * (A * f).trace ^ 2 +
            conj σ / W * (A * fᴴ).trace ^ 2) by ring, hexp, hmain, ← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
    exact herr _ fun i k => hcon i k k i
  · -- `E (Tr AU⁰)²`
    have hexp : (∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂μ) =
        ∑ i, ∑ k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          bilinearCovariance μ (freshU b E X) (v i) (v i) (v k) (v k) := by
      simp only [trace_mul_eq_sum hA.1, hcovint, sq, Finset.sum_mul_sum]
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => by
        have := (hint i i k k).const_mul ((hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ))
        refine this.congr (ae_of_all _ fun ω => ?_)
        simp only; ring]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun k _ => by
        have := (hint i i k k).const_mul ((hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ))
        refine this.congr (ae_of_all _ fun ω => ?_)
        simp only; ring]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← integral_const_mul]
      congr 1; funext ω; ring
    have hmain : (((D₀ / W : ℝ)) : ℂ) * (A * A).trace + σ / W * (A * f * A * f).trace +
        conj σ / W * (A * fᴴ * A * fᴴ).trace =
        ∑ i, ∑ k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          ((((D₀ / (2 * W) : ℝ)) : ℂ) * (crossedTensor (v i) (v i) (v k) (v k) 1 1 +
            crossedTensor (v i) (v i) (v k) (v k) 1 1) +
          σ / W * crossedTensor (v i) (v i) (v k) (v k) f f +
          conj σ / W * crossedTensor (v i) (v i) (v k) (v k) fᴴ fᴴ) := by
      simp only [crossedTensor, hbil]
      rw [trace_sandwich_two hA.1 f f, trace_sandwich_two hA.1 fᴴ fᴴ, trace_mul_self_eq_sum hA.1]
      have hterm : ∀ i k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          ((((D₀ / (2 * W) : ℝ)) : ℂ) * (rot hA.1 1 i k * rot hA.1 1 k i +
            rot hA.1 1 i k * rot hA.1 1 k i) +
            σ / W * (rot hA.1 f i k * rot hA.1 f k i) +
            conj σ / W * (rot hA.1 fᴴ i k * rot hA.1 fᴴ k i)) =
          (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) * ((((D₀ / (2 * W) : ℝ)) : ℂ) * (rot hA.1 1 i k * rot hA.1 1 k i +
            rot hA.1 1 i k * rot hA.1 1 k i)) +
            σ / W * ((hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) * (rot hA.1 f i k * rot hA.1 f k i)) +
            conj σ / W * ((hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) * (rot hA.1 fᴴ i k * rot hA.1 fᴴ k i)) := by
        intro i k; ring
      have hdiag : ∀ i, ∑ k, (hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues k : ℂ) *
          ((((D₀ / (2 * W) : ℝ)) : ℂ) * (rot hA.1 1 i k * rot hA.1 1 k i +
            rot hA.1 1 i k * rot hA.1 1 k i)) =
          (((D₀ / W : ℝ)) : ℂ) * ((hA.1.eigenvalues i : ℂ) * (hA.1.eigenvalues i : ℂ)) := by
        intro i
        rw [Finset.sum_eq_single i]
        · simp only [hrot1, ite_true]; push_cast; ring
        · intro k _ hk; simp [hrot1, Ne.symm hk]
        · simp
      simp only [hterm, Finset.sum_add_distrib, hdiag, ← Finset.mul_sum]

    rw [show (∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂μ) -
        (((D₀ / W : ℝ)) : ℂ) * (A * A).trace - σ / W * (A * f * A * f).trace -
        conj σ / W * (A * fᴴ * A * fᴴ).trace =
        (∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂μ) -
          ((((D₀ / W : ℝ)) : ℂ) * (A * A).trace + σ / W * (A * f * A * f).trace +
            conj σ / W * (A * fᴴ * A * fᴴ).trace) by ring, hexp, hmain]
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
    exact herr _ fun i k => hcon i i k k

/-!
## 4. The trace-square and square-trace bounds
-/

section Bounds

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

omit [DecidableEq n] in
/-- `|Tr(Af*)| = |Tr(Af)|` for Hermitian `A`. -/
theorem norm_trace_mul_conjTranspose (hA : A.IsHermitian) (f : Matrix n n ℂ) :
    ‖(A * fᴴ).trace‖ = ‖(A * f).trace‖ := by
  have : A * fᴴ = (f * A)ᴴ := by rw [conjTranspose_mul, hA.eq]
  rw [this, trace_conjTranspose, norm_star, trace_mul_comm]

/-- `|Tr(AfAf)| ≤ Tr(AfAf*)` for `A ⪰ 0`. -/
theorem norm_trace_sandwich_le (hA : A.PosSemidef) (f : Matrix n n ℂ) :
    ‖(A * f * A * f).trace‖ ≤ (A * f * A * fᴴ).trace.re := by
  rw [trace_sandwich_two hA.1, trace_sandwich_eq_sum hA.1, Complex.ofReal_re]
  set α := hA.1.eigenvalues
  have hα : ∀ i, 0 ≤ α i := hA.eigenvalues_nonneg
  set F := rot hA.1 f
  calc ‖∑ i, ∑ k, (α i : ℂ) * (α k : ℂ) * (F i k * F k i)‖
      ≤ ∑ i, ∑ k, α i * α k * (‖F i k‖ ^ 2 / 2 + ‖F k i‖ ^ 2 / 2) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (hα i), Real.norm_of_nonneg (hα k)]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hα i) (hα k))
        nlinarith [sq_nonneg (‖F i k‖ - ‖F k i‖)]
    _ = sandwichSum hA.1 f := by
        unfold sandwichSum
        simp only [mul_add, Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i k => α i * α k * (‖F k i‖ ^ 2 / 2))]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

/-- `|Tr(Af*Af*)| ≤ Tr(AfAf*)` for `A ⪰ 0`. -/
theorem norm_trace_sandwich_conj_le (hA : A.PosSemidef) (f : Matrix n n ℂ) :
    ‖(A * fᴴ * A * fᴴ).trace‖ ≤ (A * f * A * fᴴ).trace.re := by
  have h1 := norm_trace_sandwich_le hA fᴴ
  have h2 : (A * fᴴ * A * fᴴᴴ).trace.re = (A * f * A * fᴴ).trace.re := by
    rw [trace_sandwich_eq_sum hA.1 fᴴ, trace_sandwich_eq_sum hA.1 f]
    simp only [Complex.ofReal_re, sandwichSum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [rot_conjTranspose, conjTranspose_apply, norm_star]
    ring
  linarith

end Bounds

/-- **The covariance trace-square bound**
`|E Tr(AU⁰AU⁰) - (D₀/W)(Tr A)²| ≤ C(|Tr(Af)|²/W + [W⁻² + W⁻¹(δ₀ + δ₁)](Tr A)²)` and the
**covariance square-trace bound**
`|E (Tr AU⁰)² - (D₀/W) Tr A²| ≤ C(Tr(AfAf*)/W + [W⁻² + W⁻¹(δ₀ + δ₁)](Tr A)²)`. -/
theorem covTraceSquare_of (hcov : PassiveCovarianceContract)
    (hmix : PassiveSourceMixingContract) {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hE0 : -2 < E) (hE1 : E < 2) {s : ℂ} (hs : IsStationaryJet b E s) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ A : Matrix (Fin W) (Fin W) ℂ, A.PosSemidef →
        ‖(∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂freshLaw W b) -
            (((transportD0 b E / W : ℝ)) : ℂ) * A.trace ^ 2‖ ≤
          C * (‖(A * passiveF b E X).trace‖ ^ 2 / W +
            ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X)) *
              A.trace.re ^ 2) ∧
        ‖(∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b) -
            (((transportD0 b E / W : ℝ)) : ℂ) * (A * A).trace‖ ≤
          C * ((A * passiveF b E X * A * (passiveF b E X)ᴴ).trace.re / W +
            ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X)) *
              A.trace.re ^ 2) := by
  obtain ⟨C₀, W₀, h⟩ := covIdentities_of hcov hmix hb0 hb1 hE0 hE1 hs
  set σ := sigmaMinus b E s
  refine ⟨max C₀ 0 + 2 * ‖σ‖, W₀, fun W hW X hX A hA => ?_⟩
  obtain ⟨h1, h2⟩ := h W hW X hX A hA
  set f := passiveF b E X
  set e := (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X)
  have he : 0 ≤ e := by
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    positivity
  have hTA : 0 ≤ A.trace.re ^ 2 := sq_nonneg _
  have hC0 : C₀ * e * A.trace.re ^ 2 ≤ max C₀ 0 * (e * A.trace.re ^ 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg he hTA)
  have hW0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have hσW : ‖σ / (W : ℂ)‖ = ‖σ‖ / W := by rw [norm_div, Complex.norm_natCast]
  have hσW' : ‖(starRingEnd ℂ) σ / (W : ℂ)‖ = ‖σ‖ / W := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_conj]
  have hσ0 : 0 ≤ ‖σ‖ := norm_nonneg _
  have hmax : 0 ≤ max C₀ 0 := le_max_right _ _
  constructor
  · have hn := norm_trace_mul_conjTranspose hA.1 f
    set g := ‖(A * f).trace‖
    have hsame : ‖σ / W * (A * f).trace ^ 2 + (starRingEnd ℂ) σ / W * (A * fᴴ).trace ^ 2‖ ≤
        2 * ‖σ‖ * (g ^ 2 / W) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_pow, norm_pow, hσW, hσW', hn]
      have : ‖σ‖ / W * g ^ 2 = ‖σ‖ * (g ^ 2 / W) := by ring
      linarith
    calc ‖(∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂freshLaw W b) -
          (((transportD0 b E / W : ℝ)) : ℂ) * A.trace ^ 2‖
        ≤ ‖(∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂freshLaw W b) -
            (((transportD0 b E / W : ℝ)) : ℂ) * A.trace ^ 2 - σ / W * (A * f).trace ^ 2 -
            (starRingEnd ℂ) σ / W * (A * fᴴ).trace ^ 2‖ +
          ‖σ / W * (A * f).trace ^ 2 + (starRingEnd ℂ) σ / W * (A * fᴴ).trace ^ 2‖ := by
          refine le_trans (le_of_eq ?_) (norm_add_le _ _)
          congr 1; ring
      _ ≤ C₀ * e * A.trace.re ^ 2 + 2 * ‖σ‖ * (g ^ 2 / W) := add_le_add h1 hsame
      _ ≤ (max C₀ 0 + 2 * ‖σ‖) * (g ^ 2 / W + e * A.trace.re ^ 2) := by
          have : 0 ≤ g ^ 2 / W := by positivity
          nlinarith [mul_nonneg hmax this, mul_nonneg hσ0 (mul_nonneg he hTA)]
  · set g := (A * f * A * fᴴ).trace.re
    have hg1 := norm_trace_sandwich_le hA f
    have hg2 := norm_trace_sandwich_conj_le hA f
    have hg0 : 0 ≤ g := (norm_nonneg _).trans hg1
    have hsame : ‖σ / W * (A * f * A * f).trace +
        (starRingEnd ℂ) σ / W * (A * fᴴ * A * fᴴ).trace‖ ≤ 2 * ‖σ‖ * (g / W) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, hσW, hσW']
      have e1 : ‖σ‖ / W * ‖(A * f * A * f).trace‖ ≤ ‖σ‖ / W * g :=
        mul_le_mul_of_nonneg_left hg1 (by positivity)
      have e2 : ‖σ‖ / W * ‖(A * fᴴ * A * fᴴ).trace‖ ≤ ‖σ‖ / W * g :=
        mul_le_mul_of_nonneg_left hg2 (by positivity)
      have : ‖σ‖ / W * g = ‖σ‖ * (g / W) := by ring
      linarith
    calc ‖(∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b) -
          (((transportD0 b E / W : ℝ)) : ℂ) * (A * A).trace‖
        ≤ ‖(∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b) -
            (((transportD0 b E / W : ℝ)) : ℂ) * (A * A).trace - σ / W * (A * f * A * f).trace -
            (starRingEnd ℂ) σ / W * (A * fᴴ * A * fᴴ).trace‖ +
          ‖σ / W * (A * f * A * f).trace +
            (starRingEnd ℂ) σ / W * (A * fᴴ * A * fᴴ).trace‖ := by
          refine le_trans (le_of_eq ?_) (norm_add_le _ _)
          congr 1; ring
      _ ≤ C₀ * e * A.trace.re ^ 2 + 2 * ‖σ‖ * (g / W) := add_le_add h2 hsame
      _ ≤ (max C₀ 0 + 2 * ‖σ‖) * (g / W + e * A.trace.re ^ 2) := by
          have : 0 ≤ g / W := by positivity
          nlinarith [mul_nonneg hmax this, mul_nonneg hσ0 (mul_nonneg he hTA)]

end DetClockCov

end BlockBand.Endpoints.Clock
