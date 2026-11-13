module

public import BlockBand.Window.Transfer.ScalarFirstWindowIntegration
public import BlockBand.Window.Transfer.RealCenterRankShells
public import BlockBand.RankLocation.WindowTransferGaussianTail

/-!
# Rank localization at the physical scalar variance

The per-rank bound `E[A_α w(Nρ(λ^0_α+t-E))] ≤ B min(ε, C (a/(1+m))^q)`,
`m = |α - center|`, from the Gaussian law of the scalar, a terminal `L^q` bound `D a/N` and the
classical separation `β m/N ≤ |e_α - E|`; constants depend on `q, ρ, β, D, M, c` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory

namespace BlockBand.Window.Transfer

open BlockBand.RankLocation.WindowTransfer (gaussian_rank_tail_power)

/-- Gaussian-to-polynomial bound at the physical scalar variance: if `βm/N ≤ g` and `√n ≤ a`, then
`exp(-g²/(32σ²)) ≤ (16cq/β²)^{q/2} (a/m)^q`. -/
theorem original_variance_gaussian_rank_payment (p : BlockBand.Parameters)
    (q beta a m g : ℝ) (hq : 0 < q) (hbeta : 0 < beta) (hm : 0 < m)
    (ha : Real.sqrt (p.n : ℝ) ≤ a)
    (hsep : beta * m / (p.N : ℝ) ≤ g) :
    Real.exp (-g ^ 2 / (32 * originalScalarSigma p ^ 2)) ≤
      (16 * p.c * q / beta ^ 2) ^ (q / 2) * (a / m) ^ q := by
  have hc := p.c_pos
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hscaled : beta * m ≤ g * (p.N : ℝ) := (div_le_iff₀ hN).mp hsep
  have hg : 0 < g := lt_of_lt_of_le (div_pos (mul_pos hbeta hm) hN) hsep
  let kappa : ℝ := beta ^ 2 / (32 * p.c)
  have hkappa : 0 < kappa := by unfold kappa; positivity
  have hratio : g ^ 2 / (32 * originalScalarSigma p ^ 2) =
      ((p.N : ℝ) * g) ^ 2 / (32 * p.c * (p.n : ℝ)) := by
    rw [originalScalarSigma_sq_block]
    simp only [BlockBand.Parameters.N, Nat.cast_mul]
    field_simp
  have hsq : (beta * m) ^ 2 ≤ ((p.N : ℝ) * g) ^ 2 := by
    simpa only [mul_comm] using pow_le_pow_left₀ (mul_nonneg hbeta.le hm.le) hscaled 2
  have hexponent : kappa * m ^ 2 / (p.n : ℝ) ≤
      g ^ 2 / (32 * originalScalarSigma p ^ 2) := by
    calc
      _ = (beta * m) ^ 2 / (32 * p.c * (p.n : ℝ)) := by unfold kappa; ring
      _ ≤ ((p.N : ℝ) * g) ^ 2 / (32 * p.c * (p.n : ℝ)) :=
        div_le_div_of_nonneg_right hsq (by positivity)
      _ = _ := hratio.symm
  calc
    _ ≤ Real.exp (-kappa * m ^ 2 / (p.n : ℝ)) :=
      Real.exp_le_exp.mpr (by simpa only [neg_div, neg_mul] using neg_le_neg hexponent)
    _ ≤ (q / (2 * kappa)) ^ (q / 2) * (a / m) ^ q :=
      gaussian_rank_tail_power q kappa (p.n : ℝ) a m hq hkappa hn hm ha
    _ = _ := by
      congr 2
      unfold kappa
      field_simp
      ring

/-- Terminal rank moments at the rank-distance scale: if `βm/N ≤ g`, then
`(2/g)^q (Da/N)^q ≤ (2D/β)^q (a/m)^q`. -/
theorem terminal_rank_moment_payment (p : BlockBand.Parameters)
    (q beta D a m g : ℝ) (hq : 0 < q) (hbeta : 0 < beta) (hD : 0 ≤ D)
    (ha : 0 ≤ a) (hm : 0 < m) (hg : 0 < g)
    (hsep : beta * m / (p.N : ℝ) ≤ g) :
    (2 / g) ^ q * (D * a / (p.N : ℝ)) ^ q ≤
      (2 * D / beta) ^ q * (a / m) ^ q := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hscaled : beta * m ≤ g * (p.N : ℝ) := (div_le_iff₀ hN).mp hsep
  rw [← Real.mul_rpow (by positivity) (by positivity),
    ← Real.mul_rpow (by positivity) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ hq.le
  calc
    _ = 2 * D * a / (g * (p.N : ℝ)) := by field_simp
    _ ≤ 2 * D * a / (beta * m) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hscaled
    _ = _ := by field_simp

/-- Classical rank separation exceeds the microscopic support width: if `m ≥ 4M/(ρβ)` and
`βm/N ≤ g`, then `4M/(Nρ) ≤ g`. -/
theorem classical_rank_window_width (p : BlockBand.Parameters)
    (rho beta M m g : ℝ) (hrho : 0 < rho) (hbeta : 0 < beta)
    (hm : 4 * M / (rho * beta) ≤ m)
    (hsep : beta * m / (p.N : ℝ) ≤ g) :
    4 * (M / ((p.N : ℝ) * rho)) ≤ g := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hscaled := (div_le_iff₀ (mul_pos hrho hbeta)).mp hm
  have hgscaled := (div_le_iff₀ hN).mp hsep
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos hN hrho)).mpr
  nlinarith

/-- The large-rank constant `(2D/β)^q + (16cq/β²)^{q/2}`, depending only on `q, b, β, D`. -/
noncomputable def largeRankConstant (p : BlockBand.Parameters) (q beta D : ℝ) : ℝ :=
  (2 * D / beta) ^ q + (16 * p.c * q / beta ^ 2) ^ (q / 2)

/-- The rank cutoff `1 + 4M/(ρβ)`, uniform in `n, W, a` and `ε`; `M` is the support radius of the
window. -/
noncomputable def fixedRankCutoff (rho beta M : ℝ) : ℝ := 1 + 4 * M / (rho * beta)

/-- The all-rank constant, including the bounded small-rank region. -/
noncomputable def cappedRankConstant (p : BlockBand.Parameters) (q rho beta D M : ℝ) : ℝ :=
  (1 + fixedRankCutoff rho beta M) ^ q + (2 : ℝ) ^ q * largeRankConstant p q beta D

variable {Omega State : Type*} [MeasurableSpace Omega] [MeasurableSpace State]

/-- The large-rank window expectation, from the Gaussian law of the scalar and the terminal `L^q`
bound; `A` and `X` may be arbitrarily correlated. -/
theorem original_variance_correlated_rank_tail
    (p : BlockBand.Parameters) (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Y : Omega → State) (t : Omega → ℝ) (hY : Measurable Y) (ht : Measurable t)
    (hlaw : HasLaw t (gaussianReal 0 (scalarVariance (originalScalarSigma p))) mu)
    (hind : IndepFun Y t mu)
    (A X : State → ℝ) (hA : Measurable A) (hX : Measurable X)
    (hA0 : ∀ y, 0 ≤ A y) (hA1 : ∀ y, A y ≤ 1)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ x, w x = 1) (hw0 : ∀ x, 0 ≤ w x)
    (q rho beta D a M E e m epsilon : ℝ) (hq : 0 < q) (hrho : 0 < rho)
    (hbeta : 0 < beta) (hD : 0 ≤ D) (ha : Real.sqrt (p.n : ℝ) ≤ a)
    (hm : 0 < m) (hwidth : 4 * M / (rho * beta) ≤ m)
    (hsupp : ∀ x, w x ≠ 0 → |x| ≤ M)
    (hsep : beta * m / (p.N : ℝ) ≤ |e - E|)
    (hLp : eLpNorm (fun y => X y - e) (ENNReal.ofReal q) (mu.map Y) ≤
      ENNReal.ofReal (D * a / (p.N : ℝ)))
    (hepsilon : (∫ omega, A (Y omega) ∂mu) ≤ epsilon) :
    Integrable (fun omega => A (Y omega) *
      w ((p.N : ℝ) * rho * (X (Y omega) + t omega - E))) mu ∧
    (∫ omega, A (Y omega) * w ((p.N : ℝ) * rho * (X (Y omega) + t omega - E)) ∂mu) ≤
      scalarKernelPrefactor ((p.N : ℝ) * rho) (originalScalarSigma p) *
        min epsilon (largeRankConstant p q beta D * (a / m) ^ q) := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hsigma := originalScalarSigma_pos p
  have ha0 : 0 ≤ a := (Real.sqrt_nonneg _).trans ha
  have hg : 0 < |e - E| := lt_of_lt_of_le (div_pos (mul_pos hbeta hm) hN) hsep
  have hwgap := classical_rank_window_width p rho beta M m |e - E| hrho hbeta hwidth hsep
  have hActual := scalar_first_correlated_window_localization mu Y t hY ht
    (originalScalarSigma p) hlaw hind A X hA hX hA0 hA1 w hw hcompact hunit hw0
    ((p.N : ℝ) * rho) E M e q (D * a / (p.N : ℝ)) epsilon
    (mul_pos hN hrho) (originalScalarSigma_pos p) hq (by positivity) hsupp hg hwgap hLp hepsilon
  have hMoment := terminal_rank_moment_payment p q beta D a m |e - E| hq hbeta hD ha0 hm hg hsep
  have hGaussian := original_variance_gaussian_rank_payment p q beta a m |e - E| hq hbeta hm ha hsep
  have hTail : (2 / |e - E|) ^ q * (D * a / (p.N : ℝ)) ^ q +
      Real.exp (-|e - E| ^ 2 / (32 * originalScalarSigma p ^ 2)) ≤
      largeRankConstant p q beta D * (a / m) ^ q := by
    calc
      _ ≤ (2 * D / beta) ^ q * (a / m) ^ q +
          (16 * p.c * q / beta ^ 2) ^ (q / 2) * (a / m) ^ q := add_le_add hMoment hGaussian
      _ = _ := by unfold largeRankConstant; ring
  refine ⟨hActual.1, hActual.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (min_le_min_left epsilon hTail)
    (by unfold scalarKernelPrefactor; positivity)

/-- The capped expectation at every rank, `≤ B min(ε, C (a/(1+m))^q)`, combining the bounded
small ranks and the Gaussian and moment bounds at large ranks; `C` is independent of
`a, ε, A, X`. -/
theorem original_variance_correlated_capped_rank_tail
    (p : BlockBand.Parameters) (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Y : Omega → State) (t : Omega → ℝ) (hY : Measurable Y) (ht : Measurable t)
    (hlaw : HasLaw t (gaussianReal 0 (scalarVariance (originalScalarSigma p))) mu)
    (hind : IndepFun Y t mu)
    (A X : State → ℝ) (hA : Measurable A) (hX : Measurable X)
    (hA0 : ∀ y, 0 ≤ A y) (hA1 : ∀ y, A y ≤ 1)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ x, w x = 1) (hw0 : ∀ x, 0 ≤ w x)
    (q rho beta D a M E e m epsilon : ℝ) (hq : 0 < q) (hrho : 0 < rho)
    (hbeta : 0 < beta) (hD : 0 ≤ D) (ha : Real.sqrt (p.n : ℝ) ≤ a)
    (ha1 : 1 ≤ a) (hM : 0 ≤ M) (hm : 0 ≤ m) (hepsilon1 : epsilon ≤ 1)
    (hsupp : ∀ x, w x ≠ 0 → |x| ≤ M)
    (hsep : beta * m / (p.N : ℝ) ≤ |e - E|)
    (hLp : eLpNorm (fun y => X y - e) (ENNReal.ofReal q) (mu.map Y) ≤
      ENNReal.ofReal (D * a / (p.N : ℝ)))
    (hepsilon : (∫ omega, A (Y omega) ∂mu) ≤ epsilon) :
    Integrable (fun omega => A (Y omega) *
      w ((p.N : ℝ) * rho * (X (Y omega) + t omega - E))) mu ∧
    (∫ omega, A (Y omega) * w ((p.N : ℝ) * rho * (X (Y omega) + t omega - E)) ∂mu) ≤
      scalarKernelPrefactor ((p.N : ℝ) * rho) (originalScalarSigma p) *
        min epsilon (cappedRankConstant p q rho beta D M * (a / (1 + m)) ^ q) := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hsigma := originalScalarSigma_pos p
  have hc := p.c_pos
  have ha0 : 0 ≤ a := by linarith
  have hK : 0 ≤ largeRankConstant p q beta D := by unfold largeRankConstant; positivity
  have hR : 0 ≤ fixedRankCutoff rho beta M := by unfold fixedRankCutoff; positivity
  have hR1 : 1 ≤ fixedRankCutoff rho beta M := by
    unfold fixedRankCutoff
    have : 0 ≤ 4 * M / (rho * beta) := by positivity
    linarith
  have hSmall : (1 + fixedRankCutoff rho beta M) ^ q ≤ cappedRankConstant p q rho beta D M := by
    unfold cappedRankConstant
    have : 0 ≤ (2 : ℝ) ^ q * largeRankConstant p q beta D := by positivity
    linarith
  have hLarge : (2 : ℝ) ^ q * largeRankConstant p q beta D ≤ cappedRankConstant p q rho beta D M := by
    unfold cappedRankConstant
    have : 0 ≤ (1 + fixedRankCutoff rho beta M) ^ q := by positivity
    linarith
  by_cases hmR : m ≤ fixedRankCutoff rho beta M
  · have hCap := scalar_first_window_expectation_cap mu Y t hY ht (originalScalarSigma p)
      hlaw hind A X hA hX hA0 hA1 w hw hcompact hunit hw0
      ((p.N : ℝ) * rho) E M epsilon (mul_pos hN hrho) (originalScalarSigma_pos p) hsupp hepsilon
    rw [small_distance_capped_term_eq q a epsilon (cappedRankConstant p q rho beta D M)
      (fixedRankCutoff rho beta M) m hq ha1 hepsilon1 hR hm hmR hSmall]
    exact hCap
  · have hm1 : 1 ≤ m := hR1.trans (le_of_not_ge hmR)
    have hm0 : 0 < m := by linarith
    have hwid : 4 * M / (rho * beta) ≤ m := by
      have := le_of_not_ge hmR
      unfold fixedRankCutoff at this
      linarith
    have hActual := original_variance_correlated_rank_tail p mu Y t hY ht hlaw hind
      A X hA hX hA0 hA1 w hw hcompact hunit hw0 q rho beta D a M E e m epsilon
      hq hrho hbeta hD ha hm0 hwid hsupp hsep hLp hepsilon
    have hpay := large_distance_denominator_pay q a m hq ha0 hm1
    have htail : largeRankConstant p q beta D * (a / m) ^ q ≤
        cappedRankConstant p q rho beta D M * (a / (1 + m)) ^ q := by
      calc
        _ ≤ largeRankConstant p q beta D * ((2 : ℝ) ^ q * (a / (1 + m)) ^ q) :=
          mul_le_mul_of_nonneg_left hpay hK
        _ = ((2 : ℝ) ^ q * largeRankConstant p q beta D) * (a / (1 + m)) ^ q := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hLarge (by positivity)
    exact ⟨hActual.1, hActual.2.trans (mul_le_mul_of_nonneg_left (min_le_min_left epsilon htail)
      (by unfold scalarKernelPrefactor; positivity))⟩

end BlockBand.Window.Transfer
