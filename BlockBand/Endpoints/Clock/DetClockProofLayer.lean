module

public import BlockBand.Endpoints.Clock.DetClockProofFresh

/-!
# The deterministic-clock lemma: one step of the one-ended chain at a deterministic past

We bound the defect of one step of the expected clock determinant at a deterministic past.

Past: a deterministic Hermitian `X` (the old self-energy) and a deterministic `Q ⪰ 0` (the old
clock); one fresh one-port layer `ω ~ freshLaw W b`; the new clock is
`Q₊ = L*QL + (q/W²)C₊` (`ClockMixingProb.Q_succ`).

* `stepDefect W b E q a X Q`: `E F_a(Q₊) - F_a(Q) - W⁻¹(D₀/2 · a²∂²F_a(Q) - d q a F_a(Q))`, with
  `a²∂²F_a(Q) = F_a(Q)[(Tr A_a)² + Tr A_a²]`. This is the integrand of
  the remainder `r_{W,j}(a)` of the deterministic clock step once the past is integrated out
  (`remainder_eq_integral`).
* `pastWeight`: `Λ = 1 + γ + W(δ₀ + δ₁) + √W(|Z| + √S)` (`γ = Tr Q`, `Z = Tr(Qf)`,
  `S = Tr(QfQf*)`): every past quantity of the lemma, normalised by its size on the path
  (`OpenInputsMoments`, the clock-mixing lemma).
* `stepDefect_le`: for fixed `0 < b < 1/2`, bulk `E`, a stationary jet `s`, `K ≥ 1`, `K_q ≥ 0`,
  there are `C, W₀` with `|stepDefect| ≤ C Λ⁹ W^{-3/2}` for `W ≥ W₀`, every Hermitian `X`, every
  `Q ⪰ 0`, `a ∈ [K⁻¹, K]`, `q ∈ [0, K_q]`. On `δ₀ ≤ d` this is the computation of the paper: the
  Ward mean (`wardMean_of`) for the first-order term, the covariance identities
  (`covTraceSquare_of`), the injection mean (`injectionMean_of`), the Taylor and injection
  remainders (`fresh_expand`). On `δ₀ > d` the bound is the trivial `|stepDefect| ≤ C(1+γ²)`
  times `1 ≤ (δ₀/d)²` (no Ward mean is needed there).

The arithmetic (`numeric_domain`) is done in the normalised variables `w = W^{-1/2}`, `Λ`:
`δ₀, δ₁ ≤ Λw²`, `|Z|, √S ≤ Λw`, `γ ≤ Λ`, `‖E LL* - I‖ ≤ CΛ²w²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

/-- The one-step defect of the deterministic clock step at a deterministic past `(X, Q)`. -/
def stepDefect (W : ℕ) (b E qv a : ℝ) (X Q : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  (∫ ω, detLaplace ((freshL b E X ω)ᴴ * Q * freshL b E X ω +
      ((qv / (W : ℝ) ^ 2 : ℝ) : ℂ) • freshC b E X ω) a ∂freshLaw W b) - detLaplace Q a -
    (W : ℝ)⁻¹ * (transportD0 b E / 2 * (detLaplace Q a * ((resolventWeight Q a).trace.re ^ 2 +
      ((resolventWeight Q a) ^ 2).trace.re)) - dStar b * qv * a * detLaplace Q a)

/-- `Λ = 1 + γ + W(δ₀ + δ₁) + √W(|Z| + √S)`. -/
def pastWeight (W : ℕ) (b E : ℝ) (s : ℂ) (X Q : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  1 + Q.trace.re + W * (jetDistance0 b E X + jetDistance1 b E s X) +
    Real.sqrt W * (‖(Q * passiveF b E X).trace‖ + hsSandwich Q (passiveF b E X))

namespace DetClockProof

open ClockMixingAlg ClockMixingProb DetClockTaylor

variable {W : ℕ}

/-!
## 1. Norms of the fresh layer
-/

theorem norm_freshG12_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    ‖freshG12 b E X ω‖ ≤ ‖freshLayer b E X ω‖ := by
  have h : freshG12 b E X ω = (freshLayer b E X ω).submatrix
      (fun x : Fin W => (Sum.inl ((0 : Fin 1), x) : LayerSite W .oneBlockOnePort))
      (fun y : Fin W => (Sum.inr ((0 : Fin 1), y) : LayerSite W .oneBlockOnePort)) := by
    ext x y; rfl
  rw [h]
  refine norm_submatrix_le _ ?_ ?_
  · intro x y hxy; simpa using hxy
  · intro x y hxy; simpa using hxy

theorem norm_freshL_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    ‖freshL b E X ω‖ ≤ ‖boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ *
      ‖freshLayer b E X ω‖ := by
  have h : freshL b E X ω = (boundaryZ b E • 1 - X) * freshG12 b E X ω := rfl
  rw [h]
  exact (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left (norm_freshG12_le b E X ω)
    (norm_nonneg _))

theorem norm_freshC_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    ‖freshC b E X ω‖ ≤ ‖freshLayer b E X ω‖ ^ 2 := by
  unfold freshC
  refine (l2_opNorm_mul _ _).trans ?_
  rw [l2_opNorm_conjTranspose, sq]
  exact mul_le_mul (norm_freshG12_le b E X ω) (norm_freshG12_le b E X ω) (norm_nonneg _)
    (norm_nonneg _)

theorem integrable_freshU_apply {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ}
    (hG2 : Integrable (fun ω => ‖freshLayer b E X ω‖ ^ 2) (freshLaw W b)) (i j : Fin W) :
    Integrable (fun ω => freshU b E X ω i j) (freshLaw W b) := by
  have hm : Measurable (fun ω => freshU b E X ω) := DetClockCov.measurable_freshU b E X
  set k := ‖boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖
  refine Integrable.mono' (hG2.const_mul (k ^ 2)) (meas_entry hm i j).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  refine (norm_apply_le _ i j).trans ?_
  unfold freshU
  refine (l2_opNorm_mul _ _).trans ?_
  rw [l2_opNorm_conjTranspose]
  have h := norm_freshL_le b E X ω
  have h0 := norm_nonneg (freshL b E X ω)
  calc ‖freshL b E X ω‖ * ‖freshL b E X ω‖ ≤ (k * ‖freshLayer b E X ω‖) *
        (k * ‖freshLayer b E X ω‖) := mul_le_mul h h h0 (by positivity)
    _ = k ^ 2 * ‖freshLayer b E X ω‖ ^ 2 := by ring

/-!
## 2. Bookkeeping lemmas for the final bound
-/

/-- Raising the exponents: `x ≤ c Λ^k s^l` with `k ≤ 9`, `3 ≤ l` gives `x ≤ c Λ⁹ s³`. -/
theorem le_mono_bound {x c Λ s : ℝ} {k l : ℕ} (hc : 0 ≤ c) (hΛ : 1 ≤ Λ) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (hk : k ≤ 9) (hl : 3 ≤ l) (h : x ≤ c * Λ ^ k * s ^ l) :
    x ≤ c * Λ ^ 9 * s ^ 3 := by
  refine h.trans ?_
  have h1 : Λ ^ k ≤ Λ ^ 9 := pow_le_pow_right₀ hΛ hk
  have h2 : s ^ l ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 hl
  have h3 : 0 ≤ Λ ^ k := pow_nonneg (by linarith) k
  have h4 : 0 ≤ s ^ l := pow_nonneg hs0 l
  calc c * Λ ^ k * s ^ l ≤ c * Λ ^ 9 * s ^ l :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc) h4
    _ ≤ c * Λ ^ 9 * s ^ 3 :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hc (pow_nonneg (by linarith) 9))

/-!
## 3. The decomposition of the one-step defect
-/

/-- **Decomposition of the defect** into the expected Taylor/injection remainder, the first-order
(mean) term, the two covariance displays, and the injection mean. -/
theorem stepDefect_decomp {b E qv a : ℝ} {X Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (ha : 0 ≤ a) (hqv : 0 ≤ qv) (hW : 0 < W) {c mβ mC : ℝ} (hc : 0 ≤ c) (hmβ : 0 ≤ mβ)
    (hmC : 0 ≤ mC) (hUi : ∀ i j, Integrable (fun ω => freshU b E X ω i j) (freshLaw W b))
    (hfl : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (freshU b E X ω -
        matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal 3) (freshLaw W b) ≤
      ENNReal.ofReal (c * vecNorm u * vecNorm v))
    (hβ : eLpNorm (fun ω => (freshC b E X ω).trace.re) (ENNReal.ofReal 3) (freshLaw W b) ≤
      ENNReal.ofReal mβ)
    (hCn : eLpNorm (fun ω => ‖freshC b E X ω‖) (ENNReal.ofReal 3) (freshLaw W b) ≤
      ENNReal.ofReal mC) :
    |stepDefect W b E qv a X Q| ≤
      (a ^ 2 * ((qv / (W : ℝ) ^ 2) ^ 2 * mβ ^ 2 + qv / (W : ℝ) ^ 2 * (mC * ((1 +
          ‖matrixExpect (freshLaw W b) (freshU b E X) - 1‖ + c) * Q.trace.re))) +
        8 * a * (qv / (W : ℝ) ^ 2) * ((‖matrixExpect (freshLaw W b) (freshU b E X) - 1‖ + c) *
          (resolventWeight Q a).trace.re) * mβ +
        800 * ((‖matrixExpect (freshLaw W b) (freshU b E X) - 1‖ + c) *
          (resolventWeight Q a).trace.re) ^ 3) +
      ‖(resolventWeight Q a * (matrixExpect (freshLaw W b) (freshU b E X) - 1)).trace‖ +
      (‖matrixExpect (freshLaw W b) (freshU b E X) - 1‖ * (resolventWeight Q a).trace.re *
          (2 * c * (resolventWeight Q a).trace.re +
            ‖matrixExpect (freshLaw W b) (freshU b E X) - 1‖ * (resolventWeight Q a).trace.re) +
        ‖(∫ ω, (resolventWeight Q a * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b) -
          (((transportD0 b E / W : ℝ)) : ℂ) * (resolventWeight Q a * resolventWeight Q a).trace‖ +
        ‖(∫ ω, (resolventWeight Q a * freshU0 b E X ω * resolventWeight Q a *
            freshU0 b E X ω).trace ∂freshLaw W b) -
          (((transportD0 b E / W : ℝ)) : ℂ) * (resolventWeight Q a).trace ^ 2‖) +
      a * (qv / W) * |(∫ ω, (freshC b E X ω).trace.re ∂freshLaw W b) / W - dStar b| := by
  have hL : Measurable (fun ω => freshL b E X ω) :=
    (meas_freshL (W := W) b E).comp (f := fun ω => (X, ω)) (measurable_const.prodMk measurable_id)
  have hC : Measurable (fun ω => freshC b E X ω) :=
    (meas_freshC (W := W) b E).comp (f := fun ω => (X, ω)) (measurable_const.prodMk measurable_id)
  have hκ : 0 ≤ qv / (W : ℝ) ^ 2 := by positivity
  obtain ⟨-, -, -, -, E1, E2, E3⟩ := fresh_expand (freshLaw W b) hL hC
    (fun ω => freshC_posSemidef b E X ω) hQ ha hκ hc hmβ hmC hUi hfl hβ hCn
  set A := resolventWeight Q a with hA
  set F := detLaplace Q a with hF
  have hApsd : A.PosSemidef := resolventWeight_posSemidef hQ ha
  have hF0 : 0 < F := detLaplace_pos hQ ha
  have hF1 : F ≤ 1 := detLaplace_le_one hQ ha
  set EU := matrixExpect (freshLaw W b) (freshU b E X) with hEU
  set M := EU - 1 with hM
  set I2 := ∫ ω, tauA Q (freshL b E X ω) a ^ 2 ∂freshLaw W b with hI2
  set Iσ := ∫ ω, sigA Q (freshL b E X ω) a ∂freshLaw W b with hIσ
  set Iβ := ∫ ω, (freshC b E X ω).trace.re ∂freshLaw W b with hIβ
  set IF := ∫ ω, detLaplace ((freshL b E X ω)ᴴ * Q * freshL b E X ω +
      ((qv / (W : ℝ) ^ 2 : ℝ) : ℂ) • freshC b E X ω) a ∂freshLaw W b with hIF
  set c2 := ∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b with hc2
  set c1 := ∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂freshLaw W b with hc1
  have hD : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  set D := transportD0 b E with hDdef
  -- the defect
  have hdef : stepDefect W b E qv a X Q =
      (IF - F - (-(F * (A * M).trace.re) + F * (I2 + Iσ) / 2 - a * F * (qv / (W : ℝ) ^ 2 * Iβ))) -
        F * (A * M).trace.re + F / 2 * (I2 - D / W * ((A ^ 2).trace.re)) +
        F / 2 * (Iσ - D / W * A.trace.re ^ 2) - a * F * (qv / W) * (Iβ / W - dStar b) := by
    unfold stepDefect
    rw [← hIF, ← hF, ← hA, ← hDdef]
    field_simp
    ring
  rw [hdef]
  have hA2 : (A ^ 2).trace.re = (A * A).trace.re := by rw [pow_two]
  have hTAim : A.trace.im = 0 := im_trace_resolventWeight hQ ha
  have hcov2 : |I2 - D / W * (A ^ 2).trace.re| ≤
      ‖M‖ * A.trace.re * (2 * c * A.trace.re + ‖M‖ * A.trace.re) +
        ‖c2 - (((D / W : ℝ)) : ℂ) * (A * A).trace‖ := by
    have h1 : |c2.re - D / W * (A * A).trace.re| ≤ ‖c2 - (((D / W : ℝ)) : ℂ) * (A * A).trace‖ := by
      refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
      rw [Complex.sub_re, Complex.re_ofReal_mul]
    rw [hA2]
    calc |I2 - D / W * (A * A).trace.re| ≤ |I2 - c2.re| + |c2.re - D / W * (A * A).trace.re| := by
          have := abs_sub_le I2 c2.re (D / W * (A * A).trace.re); linarith
      _ ≤ _ := add_le_add E2 h1
  have hcov1 : |Iσ - D / W * A.trace.re ^ 2| ≤
      ‖M‖ * A.trace.re * (2 * c * A.trace.re + ‖M‖ * A.trace.re) +
        ‖c1 - (((D / W : ℝ)) : ℂ) * A.trace ^ 2‖ := by
    have hsq : (A.trace ^ 2).re = A.trace.re ^ 2 := by
      rw [pow_two, Complex.mul_re, hTAim]; ring
    have h1 : |c1.re - D / W * A.trace.re ^ 2| ≤ ‖c1 - (((D / W : ℝ)) : ℂ) * A.trace ^ 2‖ := by
      refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
      rw [Complex.sub_re, Complex.re_ofReal_mul, hsq]
    calc |Iσ - D / W * A.trace.re ^ 2| ≤ |Iσ - c1.re| + |c1.re - D / W * A.trace.re ^ 2| := by
          have := abs_sub_le Iσ c1.re (D / W * A.trace.re ^ 2); linarith
      _ ≤ _ := add_le_add E3 h1
  have hm : |(A * M).trace.re| ≤ ‖(A * M).trace‖ := Complex.abs_re_le_norm _
  set R1 := a ^ 2 * ((qv / (W : ℝ) ^ 2) ^ 2 * mβ ^ 2 + qv / (W : ℝ) ^ 2 * (mC * ((1 + ‖M‖ + c) *
      Q.trace.re))) + 8 * a * (qv / (W : ℝ) ^ 2) * ((‖M‖ + c) * A.trace.re) * mβ +
      800 * ((‖M‖ + c) * A.trace.re) ^ 3 with hR1
  have t1 := E1
  have t2 : |F * (A * M).trace.re| ≤ ‖(A * M).trace‖ := by
    rw [abs_mul, abs_of_pos hF0]
    exact (mul_le_of_le_one_left (abs_nonneg _) hF1).trans hm
  have hhalf : ∀ x B : ℝ, |x| ≤ B → |F / 2 * x| ≤ B / 2 := by
    intro x B hx
    have hB : 0 ≤ B := (abs_nonneg _).trans hx
    rw [abs_mul, abs_of_pos (by positivity : 0 < F / 2)]
    calc F / 2 * |x| ≤ F / 2 * B := mul_le_mul_of_nonneg_left hx (by positivity)
      _ ≤ 1 / 2 * B := mul_le_mul_of_nonneg_right (by linarith) hB
      _ = B / 2 := by ring
  have t3 := hhalf _ _ hcov2
  have t4 := hhalf _ _ hcov1
  have t5 : |a * F * (qv / W) * (Iβ / W - dStar b)| ≤ a * (qv / W) * |Iβ / W - dStar b| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_pos hF0,
      abs_of_nonneg (by positivity : 0 ≤ qv / (W : ℝ))]
    have h0 : 0 ≤ a * (qv / W) * |Iβ / W - dStar b| := by positivity
    calc a * F * (qv / W) * |Iβ / W - dStar b| = F * (a * (qv / W) * |Iβ / W - dStar b|) := by
          ring
      _ ≤ 1 * (a * (qv / W) * |Iβ / W - dStar b|) := mul_le_mul_of_nonneg_right hF1 h0
      _ = _ := one_mul _
  calc |IF - F - (-(F * (A * M).trace.re) + F * (I2 + Iσ) / 2 - a * F * (qv / (W : ℝ) ^ 2 * Iβ)) -
        F * (A * M).trace.re + F / 2 * (I2 - D / W * (A ^ 2).trace.re) +
        F / 2 * (Iσ - D / W * A.trace.re ^ 2) - a * F * (qv / W) * (Iβ / W - dStar b)|
      ≤ |IF - F - (-(F * (A * M).trace.re) + F * (I2 + Iσ) / 2 -
          a * F * (qv / (W : ℝ) ^ 2 * Iβ))| + |F * (A * M).trace.re| +
        |F / 2 * (I2 - D / W * (A ^ 2).trace.re)| + |F / 2 * (Iσ - D / W * A.trace.re ^ 2)| +
        |a * F * (qv / W) * (Iβ / W - dStar b)| := by
        have a1 := abs_add_le (IF - F - (-(F * (A * M).trace.re) + F * (I2 + Iσ) / 2 -
          a * F * (qv / (W : ℝ) ^ 2 * Iβ)) - F * (A * M).trace.re +
          F / 2 * (I2 - D / W * (A ^ 2).trace.re)) (F / 2 * (Iσ - D / W * A.trace.re ^ 2))
        have a2 := abs_add_le (IF - F - (-(F * (A * M).trace.re) + F * (I2 + Iσ) / 2 -
          a * F * (qv / (W : ℝ) ^ 2 * Iβ)) - F * (A * M).trace.re)
          (F / 2 * (I2 - D / W * (A ^ 2).trace.re))
        have a3 := abs_sub (IF - F - (-(F * (A * M).trace.re) + F * (I2 + Iσ) / 2 -
          a * F * (qv / (W : ℝ) ^ 2 * Iβ))) (F * (A * M).trace.re)
        have a4 := abs_sub (IF - F - (-(F * (A * M).trace.re) + F * (I2 + Iσ) / 2 -
          a * F * (qv / (W : ℝ) ^ 2 * Iβ)) - F * (A * M).trace.re +
          F / 2 * (I2 - D / W * (A ^ 2).trace.re) + F / 2 * (Iσ - D / W * A.trace.re ^ 2))
          (a * F * (qv / W) * (Iβ / W - dStar b))
        linarith
    _ ≤ _ := by
        have t1' : |IF - F - (-(F * (A * M).trace.re) + F * (I2 + Iσ) / 2 -
            a * F * (qv / (W : ℝ) ^ 2 * Iβ))| ≤ R1 := E1
        have hn1 := norm_nonneg (c2 - (((D / W : ℝ)) : ℂ) * (A * A).trace)
        have hn2 := norm_nonneg (c1 - (((D / W : ℝ)) : ℂ) * A.trace ^ 2)
        have hTA : 0 ≤ A.trace.re := trace_re_nonneg hApsd
        have hE2b : 0 ≤ ‖M‖ * A.trace.re * (2 * c * A.trace.re + ‖M‖ * A.trace.re) := by
          positivity
        linarith

/-!
## 4. The numerical bound on the scalar domain
-/

/-- `0 ≤ x ≤ X`, `0 ≤ y ≤ Y` give `xy ≤ XY`. -/
theorem mul_le_mul_nn {x y X Y : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ X) (hy0 : 0 ≤ y) (hy : y ≤ Y) :
    x * y ≤ X * Y := mul_le_mul hx hy hy0 (hx0.trans hx)

section Numeric

variable {Λ w : ℝ}

theorem nb_w (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {k l : ℕ} (hkl : k ≤ l) : w ^ l ≤ w ^ k :=
  pow_le_pow_of_le_one hw0 hw1 hkl

theorem nb_Lambda (hΛ : 1 ≤ Λ) {k l : ℕ} (hkl : k ≤ l) : Λ ^ k ≤ Λ ^ l := pow_le_pow_right₀ hΛ hkl

/-- Term 1 of `stepDefect_decomp`. -/
theorem nb_t1 {K Kq CA CM Cf a κ mβ nM c γ : ℝ} (hΛ : 1 ≤ Λ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hKq : 0 ≤ Kq) (_hCA : 0 ≤ CA) (hCM : 0 ≤ CM) (hCf : 0 ≤ Cf) (ha0 : 0 ≤ a) (haK : a ≤ K)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ Kq * w ^ 4) (hmβ0 : 0 ≤ mβ) (hκmβ : κ * mβ ≤ Kq * CA ^ 2 * w ^ 2)
    (hM0 : 0 ≤ nM) (hc0 : 0 ≤ c) (hMc : nM + c ≤ (CM + Cf) * Λ ^ 2 * w) (hγ0 : 0 ≤ γ)
    (hγ : γ ≤ Λ) :
    a ^ 2 * (κ ^ 2 * mβ ^ 2 + κ * (CA ^ 2 * ((1 + nM + c) * γ))) ≤
      K ^ 2 * (Kq ^ 2 * CA ^ 4 + Kq * CA ^ 2 * (1 + CM + Cf)) * Λ ^ 9 * w ^ 3 := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hΛ21 : (1 : ℝ) ≤ Λ ^ 2 := one_le_pow₀ hΛ
  have e1 : κ ^ 2 * mβ ^ 2 ≤ (Kq * CA ^ 2 * w ^ 2) ^ 2 := by
    rw [show κ ^ 2 * mβ ^ 2 = (κ * mβ) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) hκmβ 2
  have e2 : 1 + nM + c ≤ (1 + CM + Cf) * Λ ^ 2 := by
    have h1 : nM + c ≤ (CM + Cf) * Λ ^ 2 := hMc.trans (by
      have := mul_le_mul_of_nonneg_left hw1 (by positivity : 0 ≤ (CM + Cf) * Λ ^ 2)
      linarith)
    have : (1 : ℝ) * 1 ≤ 1 * Λ ^ 2 := by linarith
    have e : (1 + CM + Cf) * Λ ^ 2 = Λ ^ 2 + (CM + Cf) * Λ ^ 2 := by ring
    linarith
  have e3 : κ * (CA ^ 2 * ((1 + nM + c) * γ)) ≤
      (Kq * w ^ 4) * (CA ^ 2 * (((1 + CM + Cf) * Λ ^ 2) * Λ)) := by
    refine mul_le_mul_nn hκ0 hκ (by positivity) ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_nn (by positivity) e2 hγ0 hγ) (sq_nonneg _)
  have e4 : a ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ ha0 haK 2
  have e5 : (Kq * CA ^ 2 * w ^ 2) ^ 2 ≤ Kq ^ 2 * CA ^ 4 * Λ ^ 3 * w ^ 4 := by
    have h3 : (1 : ℝ) ≤ Λ ^ 3 := one_le_pow₀ hΛ
    have h0 : 0 ≤ Kq ^ 2 * CA ^ 4 * w ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_left h3 h0
    calc (Kq * CA ^ 2 * w ^ 2) ^ 2 = Kq ^ 2 * CA ^ 4 * w ^ 4 * 1 := by ring
      _ ≤ Kq ^ 2 * CA ^ 4 * w ^ 4 * Λ ^ 3 := this
      _ = _ := by ring
  have e6 : κ ^ 2 * mβ ^ 2 + κ * (CA ^ 2 * ((1 + nM + c) * γ)) ≤
      (Kq ^ 2 * CA ^ 4 + Kq * CA ^ 2 * (1 + CM + Cf)) * Λ ^ 3 * w ^ 4 := by
    have : (Kq * w ^ 4) * (CA ^ 2 * (((1 + CM + Cf) * Λ ^ 2) * Λ)) =
        Kq * CA ^ 2 * (1 + CM + Cf) * Λ ^ 3 * w ^ 4 := by ring
    have e : (Kq ^ 2 * CA ^ 4 + Kq * CA ^ 2 * (1 + CM + Cf)) * Λ ^ 3 * w ^ 4 =
        Kq ^ 2 * CA ^ 4 * Λ ^ 3 * w ^ 4 + Kq * CA ^ 2 * (1 + CM + Cf) * Λ ^ 3 * w ^ 4 := by ring
    linarith
  have e7 := mul_le_mul_nn (sq_nonneg a) e4 (by positivity) e6
  exact le_mono_bound (k := 3) (l := 4) (by positivity) hΛ hw0 hw1 (by norm_num) (by norm_num)
    (e7.trans (le_of_eq (by ring)))

/-- The arithmetic of the scalar-domain bound (all quantities normalised by `w = W^{-1/2}` and
`Λ`): every term of `stepDefect_decomp` is `O(Λ⁹ w³)`. -/
theorem numeric_domain {K Kq Kf Cw Cf Cc Ci CA a qv γ δ₀ δ₁ TA tAf sAf nΩ nM c mβ κ nAM
    cov1 cov2 injE : ℝ}
    (hΛ : 1 ≤ Λ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hK : 1 ≤ K) (hKq : 0 ≤ Kq) (hKf : 0 ≤ Kf)
    (hCw : 0 ≤ Cw) (hCf : 0 ≤ Cf) (hCc : 0 ≤ Cc) (hCi : 0 ≤ Ci) (hCA : 0 ≤ CA)
    (ha0 : 0 ≤ a) (haK : a ≤ K) (hqv0 : 0 ≤ qv) (hqvK : qv ≤ Kq)
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ Λ) (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ Λ * w ^ 2) (hδ10 : 0 ≤ δ₁)
    (hδ1 : δ₁ ≤ Λ * w ^ 2) (hTA0 : 0 ≤ TA) (hTA : TA ≤ K * Λ) (htAf0 : 0 ≤ tAf)
    (htAf : tAf ≤ 2 * K ^ 2 * Λ ^ 2 * w) (_hsAf0 : 0 ≤ sAf) (hsAf : sAf ≤ K ^ 2 * Λ ^ 2 * w ^ 2)
    (hΩ0 : 0 ≤ nΩ) (hΩ : nΩ ≤ 2 * Cw * Λ * w ^ 2) (hM0 : 0 ≤ nM)
    (hM : nM ≤ (4 * Cw * Kf + 2 * Cw) * Λ ^ 2 * w ^ 2) (hc : c = Cf * w) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ Kq * w ^ 4) (hmβ0 : 0 ≤ mβ) (hκmβ : κ * mβ ≤ Kq * CA ^ 2 * w ^ 2)
    (hAM : nAM ≤ 2 * nΩ * tAf + Cw * (δ₀ ^ 2 + w ^ 4) * TA)
    (hcov2 : cov2 ≤ Cc * (sAf * w ^ 2 + (w ^ 4 + w ^ 2 * (δ₀ + δ₁)) * TA ^ 2))
    (hcov1 : cov1 ≤ Cc * (tAf ^ 2 * w ^ 2 + (w ^ 4 + w ^ 2 * (δ₀ + δ₁)) * TA ^ 2))
    (hinj0 : 0 ≤ injE) (hinj : injE ≤ Ci * (δ₀ + w ^ 4)) :
    (a ^ 2 * (κ ^ 2 * mβ ^ 2 + κ * (CA ^ 2 * ((1 + nM + c) * γ))) +
        8 * a * κ * ((nM + c) * TA) * mβ + 800 * ((nM + c) * TA) ^ 3) + nAM +
      (nM * TA * (2 * c * TA + nM * TA) + cov2 + cov1) + a * (qv * w ^ 2) * injE ≤
    (K ^ 2 * (Kq ^ 2 * CA ^ 4 + Kq * CA ^ 2 * (1 + (4 * Cw * Kf + 2 * Cw) + Cf)) +
      8 * K * Kq * CA ^ 2 * (((4 * Cw * Kf + 2 * Cw) + Cf) * K) +
      800 * (((4 * Cw * Kf + 2 * Cw) + Cf) * K) ^ 3 + (8 * Cw * K ^ 2 + 2 * Cw * K) +
      (4 * Cw * Kf + 2 * Cw) * K ^ 2 * (2 * Cf + (4 * Cw * Kf + 2 * Cw)) + Cc * K ^ 2 * 4 +
      Cc * (4 * K ^ 4 + 3 * K ^ 2) + 2 * K * Kq * Ci) * Λ ^ 9 * w ^ 3 := by
  set CM := 4 * Cw * Kf + 2 * Cw with hCM
  have hCM0 : 0 ≤ CM := by positivity
  have hΛ0 : 0 ≤ Λ := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hw21 : w ^ 2 ≤ w ^ 1 := nb_w hw0 hw1 (by norm_num)
  rw [pow_one] at hw21
  have hΛ21 : (1 : ℝ) ≤ Λ ^ 2 := one_le_pow₀ hΛ
  -- `‖M‖ + c ≤ (CM + Cf) Λ² w`
  have hMc : nM + c ≤ (CM + Cf) * Λ ^ 2 * w := by
    have h1 : nM ≤ CM * Λ ^ 2 * w :=
      hM.trans (mul_le_mul_of_nonneg_left hw21 (by positivity))
    have h2 : c ≤ Cf * Λ ^ 2 * w := by
      rw [hc]
      have := mul_le_mul_of_nonneg_left hΛ21 (by positivity : 0 ≤ Cf * w)
      calc Cf * w = Cf * w * 1 := by ring
        _ ≤ Cf * w * Λ ^ 2 := this
        _ = Cf * Λ ^ 2 * w := by ring
    have e : (CM + Cf) * Λ ^ 2 * w = CM * Λ ^ 2 * w + Cf * Λ ^ 2 * w := by ring
    linarith
  have hMc0 : 0 ≤ nM + c := by positivity
  set Cτ := (CM + Cf) * K with hCτ
  have hτ : (nM + c) * TA ≤ Cτ * Λ ^ 3 * w := by
    calc (nM + c) * TA ≤ ((CM + Cf) * Λ ^ 2 * w) * (K * Λ) := mul_le_mul_nn hMc0 hMc hTA0 hTA
      _ = Cτ * Λ ^ 3 * w := by rw [hCτ]; ring
  have hτ0 : 0 ≤ (nM + c) * TA := by positivity
  have hCτ0 : 0 ≤ Cτ := by positivity
  have t1 := nb_t1 hΛ hw0 hw1 hKq hCA hCM0 hCf ha0 haK hκ0 hκ hmβ0 hκmβ hM0 hc0 hMc hγ0 hγ
  -- term 2: `8aκ mτ mβ`
  have t2 : 8 * a * κ * ((nM + c) * TA) * mβ ≤ 8 * K * Kq * CA ^ 2 * Cτ * Λ ^ 9 * w ^ 3 := by
    have e1 : 8 * a * κ * ((nM + c) * TA) * mβ = 8 * a * (κ * mβ) * ((nM + c) * TA) := by ring
    have e2 : 8 * a * (κ * mβ) ≤ 8 * K * (Kq * CA ^ 2 * w ^ 2) :=
      mul_le_mul_nn (by positivity) (by linarith) (by positivity) hκmβ
    have e3 := mul_le_mul_nn (by positivity) e2 hτ0 hτ
    rw [e1]
    exact le_mono_bound (k := 3) (l := 3) (by positivity) hΛ hw0 hw1 (by norm_num) le_rfl
      (e3.trans (le_of_eq (by ring)))
  -- term 3: `800 mτ³`
  have t3 : 800 * ((nM + c) * TA) ^ 3 ≤ 800 * Cτ ^ 3 * Λ ^ 9 * w ^ 3 := by
    have h := pow_le_pow_left₀ hτ0 hτ 3
    have e : (Cτ * Λ ^ 3 * w) ^ 3 = Cτ ^ 3 * Λ ^ 9 * w ^ 3 := by ring
    rw [e] at h
    have := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 800)
    linarith
  -- term 4: the first-order (Ward mean) term
  have t4 : nAM ≤ (8 * Cw * K ^ 2 + 2 * Cw * K) * Λ ^ 9 * w ^ 3 := by
    have e1 : 2 * nΩ * tAf ≤ 2 * ((2 * Cw * Λ * w ^ 2) * (2 * K ^ 2 * Λ ^ 2 * w)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_nn hΩ0 hΩ htAf0 htAf) (by norm_num)
    have h1 : δ₀ ^ 2 ≤ (Λ * w ^ 2) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
    have h2 : w ^ 4 ≤ Λ ^ 2 * w ^ 4 := by
      have := mul_le_mul_of_nonneg_right hΛ21 (pow_nonneg hw0 4)
      linarith
    have h3 : δ₀ ^ 2 + w ^ 4 ≤ 2 * Λ ^ 2 * w ^ 4 := by
      have e : (Λ * w ^ 2) ^ 2 = Λ ^ 2 * w ^ 4 := by ring
      linarith
    have e2 : Cw * (δ₀ ^ 2 + w ^ 4) * TA ≤ Cw * (2 * Λ ^ 2 * w ^ 4) * (K * Λ) :=
      mul_le_mul_nn (by positivity) (mul_le_mul_of_nonneg_left h3 hCw) hTA0 hTA
    have f1 : 2 * nΩ * tAf ≤ 8 * Cw * K ^ 2 * Λ ^ 9 * w ^ 3 :=
      le_mono_bound (k := 3) (l := 3) (by positivity) hΛ hw0 hw1 (by norm_num) le_rfl
        (e1.trans (le_of_eq (by ring)))
    have f2 : Cw * (δ₀ ^ 2 + w ^ 4) * TA ≤ 2 * Cw * K * Λ ^ 9 * w ^ 3 :=
      le_mono_bound (k := 3) (l := 4) (by positivity) hΛ hw0 hw1 (by norm_num) (by norm_num)
        (e2.trans (le_of_eq (by ring)))
    have e : (8 * Cw * K ^ 2 + 2 * Cw * K) * Λ ^ 9 * w ^ 3 =
        8 * Cw * K ^ 2 * Λ ^ 9 * w ^ 3 + 2 * Cw * K * Λ ^ 9 * w ^ 3 := by ring
    linarith
  -- term 5: the mean part of the second moments
  have t5 : nM * TA * (2 * c * TA + nM * TA) ≤
      CM * K ^ 2 * (2 * Cf + CM) * Λ ^ 9 * w ^ 3 := by
    have h2 : nM * TA ≤ (CM * Λ ^ 2 * w ^ 2) * (K * Λ) := mul_le_mul_nn hM0 hM hTA0 hTA
    have h1 : 2 * c * TA ≤ 2 * (Cf * w) * (K * Λ) := by
      rw [hc]; exact mul_le_mul_of_nonneg_left hTA (by positivity)
    have hΛ13 : Λ ^ 1 ≤ Λ ^ 3 := nb_Lambda hΛ (by norm_num)
    rw [pow_one] at hΛ13
    have h3 : 2 * (Cf * w) * (K * Λ) ≤ 2 * Cf * K * w * Λ ^ 3 := by
      have := mul_le_mul_of_nonneg_left hΛ13 (by positivity : 0 ≤ 2 * Cf * K * w)
      calc 2 * (Cf * w) * (K * Λ) = 2 * Cf * K * w * Λ := by ring
        _ ≤ _ := this
    have h4 : (CM * Λ ^ 2 * w ^ 2) * (K * Λ) ≤ CM * K * w * Λ ^ 3 := by
      have := mul_le_mul_of_nonneg_left hw21 (by positivity : 0 ≤ CM * K * Λ ^ 3)
      calc (CM * Λ ^ 2 * w ^ 2) * (K * Λ) = CM * K * Λ ^ 3 * w ^ 2 := by ring
        _ ≤ CM * K * Λ ^ 3 * w := this
        _ = _ := by ring
    have e1 : 2 * c * TA + nM * TA ≤ (2 * Cf + CM) * K * w * Λ ^ 3 := by
      have e : (2 * Cf + CM) * K * w * Λ ^ 3 = 2 * Cf * K * w * Λ ^ 3 + CM * K * w * Λ ^ 3 := by
        ring
      linarith
    have e3 := mul_le_mul_nn (by positivity) h2 (by positivity) e1
    exact le_mono_bound (k := 6) (l := 3) (by positivity) hΛ hw0 hw1 (by norm_num) le_rfl
      (e3.trans (le_of_eq (by ring)))
  -- terms 6, 7: the covariance errors
  have hDw : w ^ 4 + w ^ 2 * (δ₀ + δ₁) ≤ 3 * Λ * w ^ 4 := by
    have h1 : w ^ 2 * (δ₀ + δ₁) ≤ w ^ 2 * (2 * Λ * w ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : w ^ 4 ≤ Λ * w ^ 4 := by
      have := mul_le_mul_of_nonneg_right hΛ (pow_nonneg hw0 4); linarith
    have e : w ^ 2 * (2 * Λ * w ^ 2) = 2 * Λ * w ^ 4 := by ring
    linarith
  have hTA2 : TA ^ 2 ≤ K ^ 2 * Λ ^ 2 := by
    have := pow_le_pow_left₀ hTA0 hTA 2
    rw [mul_pow] at this; exact this
  have hDTA : (w ^ 4 + w ^ 2 * (δ₀ + δ₁)) * TA ^ 2 ≤ 3 * K ^ 2 * Λ ^ 3 * w ^ 4 := by
    have := mul_le_mul_nn (by positivity) hDw (sq_nonneg _) hTA2
    exact this.trans (le_of_eq (by ring))
  have hΛ23 : Λ ^ 2 ≤ Λ ^ 3 := nb_Lambda hΛ (by norm_num)
  have hΛ34 : Λ ^ 3 ≤ Λ ^ 4 := nb_Lambda hΛ (by norm_num)
  have t6 : cov2 ≤ Cc * K ^ 2 * 4 * Λ ^ 9 * w ^ 3 := by
    have e1 : sAf * w ^ 2 ≤ K ^ 2 * Λ ^ 3 * w ^ 4 := by
      have h := mul_le_mul_of_nonneg_right hsAf (sq_nonneg w)
      have h' := mul_le_mul_of_nonneg_left hΛ23 (by positivity : 0 ≤ K ^ 2 * w ^ 4)
      calc sAf * w ^ 2 ≤ K ^ 2 * Λ ^ 2 * w ^ 2 * w ^ 2 := h
        _ = K ^ 2 * w ^ 4 * Λ ^ 2 := by ring
        _ ≤ K ^ 2 * w ^ 4 * Λ ^ 3 := h'
        _ = _ := by ring
    have e2 : cov2 ≤ Cc * K ^ 2 * 4 * Λ ^ 3 * w ^ 4 := by
      refine hcov2.trans ?_
      have := mul_le_mul_of_nonneg_left (add_le_add e1 hDTA) hCc
      exact this.trans (le_of_eq (by ring))
    exact le_mono_bound (k := 3) (l := 4) (by positivity) hΛ hw0 hw1 (by norm_num) (by norm_num)
      e2
  have t7 : cov1 ≤ Cc * (4 * K ^ 4 + 3 * K ^ 2) * Λ ^ 9 * w ^ 3 := by
    have e1 : tAf ^ 2 * w ^ 2 ≤ 4 * K ^ 4 * Λ ^ 4 * w ^ 4 := by
      have h := pow_le_pow_left₀ htAf0 htAf 2
      have h2 := mul_le_mul_of_nonneg_right h (sq_nonneg w)
      exact h2.trans (le_of_eq (by ring))
    have h3 : 3 * K ^ 2 * Λ ^ 3 * w ^ 4 ≤ 3 * K ^ 2 * Λ ^ 4 * w ^ 4 := by
      have := mul_le_mul_of_nonneg_left hΛ34 (by positivity : 0 ≤ 3 * K ^ 2 * w ^ 4)
      calc 3 * K ^ 2 * Λ ^ 3 * w ^ 4 = 3 * K ^ 2 * w ^ 4 * Λ ^ 3 := by ring
        _ ≤ 3 * K ^ 2 * w ^ 4 * Λ ^ 4 := this
        _ = _ := by ring
    have e2 : cov1 ≤ Cc * (4 * K ^ 4 + 3 * K ^ 2) * Λ ^ 4 * w ^ 4 := by
      refine hcov1.trans ?_
      have := mul_le_mul_of_nonneg_left (add_le_add e1 (hDTA.trans h3)) hCc
      exact this.trans (le_of_eq (by ring))
    exact le_mono_bound (k := 4) (l := 4) (by positivity) hΛ hw0 hw1 (by norm_num) (by norm_num)
      e2
  -- term 8: the injection mean
  have t8 : a * (qv * w ^ 2) * injE ≤ 2 * K * Kq * Ci * Λ ^ 9 * w ^ 3 := by
    have hw42 : w ^ 4 ≤ w ^ 2 := nb_w hw0 hw1 (by norm_num)
    have e1 : injE ≤ Ci * (2 * Λ * w ^ 2) := by
      refine hinj.trans (mul_le_mul_of_nonneg_left ?_ hCi)
      have : w ^ 2 ≤ Λ * w ^ 2 := by
        have := mul_le_mul_of_nonneg_right hΛ (sq_nonneg w); linarith
      linarith
    have e2 : a * (qv * w ^ 2) ≤ K * (Kq * w ^ 2) :=
      mul_le_mul_nn ha0 haK (by positivity) (mul_le_mul_of_nonneg_right hqvK (sq_nonneg w))
    have e3 := mul_le_mul_nn (by positivity) e2 hinj0 e1
    exact le_mono_bound (k := 1) (l := 4) (by positivity) hΛ hw0 hw1 (by norm_num) (by norm_num)
      (e3.trans (le_of_eq (by ring)))
  rw [hCτ] at t2 t3
  have e : (K ^ 2 * (Kq ^ 2 * CA ^ 4 + Kq * CA ^ 2 * (1 + CM + Cf)) +
      8 * K * Kq * CA ^ 2 * ((CM + Cf) * K) + 800 * ((CM + Cf) * K) ^ 3 +
      (8 * Cw * K ^ 2 + 2 * Cw * K) + CM * K ^ 2 * (2 * Cf + CM) + Cc * K ^ 2 * 4 +
      Cc * (4 * K ^ 4 + 3 * K ^ 2) + 2 * K * Kq * Ci) * Λ ^ 9 * w ^ 3 =
      K ^ 2 * (Kq ^ 2 * CA ^ 4 + Kq * CA ^ 2 * (1 + CM + Cf)) * Λ ^ 9 * w ^ 3 +
      8 * K * Kq * CA ^ 2 * ((CM + Cf) * K) * Λ ^ 9 * w ^ 3 +
      800 * ((CM + Cf) * K) ^ 3 * Λ ^ 9 * w ^ 3 + (8 * Cw * K ^ 2 + 2 * Cw * K) * Λ ^ 9 * w ^ 3 +
      CM * K ^ 2 * (2 * Cf + CM) * Λ ^ 9 * w ^ 3 + Cc * K ^ 2 * 4 * Λ ^ 9 * w ^ 3 +
      Cc * (4 * K ^ 4 + 3 * K ^ 2) * Λ ^ 9 * w ^ 3 + 2 * K * Kq * Ci * Λ ^ 9 * w ^ 3 := by ring
  rw [e]
  linarith

end Numeric

/-!
## 5. The scalar domain and its complement
-/

/-- The constant of the scalar-domain bound. -/
def domConst (K Kq Kf Cw Cf Cc Ci CA : ℝ) : ℝ :=
  K ^ 2 * (Kq ^ 2 * CA ^ 4 + Kq * CA ^ 2 * (1 + (4 * Cw * Kf + 2 * Cw) + Cf)) +
    8 * K * Kq * CA ^ 2 * (((4 * Cw * Kf + 2 * Cw) + Cf) * K) +
    800 * (((4 * Cw * Kf + 2 * Cw) + Cf) * K) ^ 3 + (8 * Cw * K ^ 2 + 2 * Cw * K) +
    (4 * Cw * Kf + 2 * Cw) * K ^ 2 * (2 * Cf + (4 * Cw * Kf + 2 * Cw)) + Cc * K ^ 2 * 4 +
    Cc * (4 * K ^ 4 + 3 * K ^ 2) + 2 * K * Kq * Ci

theorem domConst_nonneg {K Kq Kf Cw Cf Cc Ci CA : ℝ} (hK : 0 ≤ K) (hKq : 0 ≤ Kq) (hKf : 0 ≤ Kf)
    (hCw : 0 ≤ Cw) (hCf : 0 ≤ Cf) (hCc : 0 ≤ Cc) (hCi : 0 ≤ Ci) :
    0 ≤ domConst K Kq Kf Cw Cf Cc Ci CA := by
  unfold domConst; positivity

/-- **The defect on the scalar domain** (deterministic assembly): the decomposition, the Ward
mean, the covariance identities and the injection mean give `|stepDefect| ≤ C Λ⁹ W^{-3/2}`. -/
theorem stepDefect_domain {b E qv a K Kq Kf Cw Cf Cc Ci CA : ℝ} {s : ℂ}
    {X Q : Matrix (Fin W) (Fin W) ℂ} (hW : 1 ≤ (W : ℝ)) (hQ : Q.PosSemidef) (hK : 1 ≤ K)
    (hKq : 0 ≤ Kq) (ha : a ∈ Set.Icc K⁻¹ K) (hqv : qv ∈ Set.Icc 0 Kq) (hCw : 0 ≤ Cw)
    (hCf : 0 ≤ Cf) (hCc : 0 ≤ Cc) (hCi : 0 ≤ Ci) (hCA : 0 ≤ CA) (hKf0 : 0 ≤ Kf)
    (hKf : ‖passiveF b E X‖ ≤ Kf) (Ω : ℂ)
    (hΩ : ‖Ω‖ ≤ Cw * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2))
    (hRem : ‖matrixExpect (freshLaw W b) (freshU b E X) - 1 - Ω • passiveF b E X -
        (starRingEnd ℂ) Ω • (passiveF b E X)ᴴ‖ ≤
      Cw * (jetDistance0 b E X ^ 2 + ((W : ℝ)⁻¹) ^ 2))
    (hcov : ‖(∫ ω, (resolventWeight Q a * freshU0 b E X ω * resolventWeight Q a *
          freshU0 b E X ω).trace ∂freshLaw W b) -
          (((transportD0 b E / W : ℝ)) : ℂ) * (resolventWeight Q a).trace ^ 2‖ ≤
        Cc * (‖(resolventWeight Q a * passiveF b E X).trace‖ ^ 2 / W +
          ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X)) *
            (resolventWeight Q a).trace.re ^ 2) ∧
      ‖(∫ ω, (resolventWeight Q a * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b) -
          (((transportD0 b E / W : ℝ)) : ℂ) * (resolventWeight Q a * resolventWeight Q a).trace‖ ≤
        Cc * ((resolventWeight Q a * passiveF b E X * resolventWeight Q a *
            (passiveF b E X)ᴴ).trace.re / W +
          ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X)) *
            (resolventWeight Q a).trace.re ^ 2))
    (hinj : |(∫ ω, (freshC b E X ω).trace.re ∂freshLaw W b) / W - dStar b| ≤
      Ci * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2))
    (hdec : |stepDefect W b E qv a X Q| ≤
      (a ^ 2 * ((qv / (W : ℝ) ^ 2) ^ 2 * ((W : ℝ) * CA ^ 2) ^ 2 + qv / (W : ℝ) ^ 2 *
          (CA ^ 2 * ((1 + ‖matrixExpect (freshLaw W b) (freshU b E X) - 1‖ +
            Cf * (Real.sqrt W)⁻¹) * Q.trace.re))) +
        8 * a * (qv / (W : ℝ) ^ 2) * ((‖matrixExpect (freshLaw W b) (freshU b E X) - 1‖ +
          Cf * (Real.sqrt W)⁻¹) * (resolventWeight Q a).trace.re) * ((W : ℝ) * CA ^ 2) +
        800 * ((‖matrixExpect (freshLaw W b) (freshU b E X) - 1‖ + Cf * (Real.sqrt W)⁻¹) *
          (resolventWeight Q a).trace.re) ^ 3) +
      ‖(resolventWeight Q a * (matrixExpect (freshLaw W b) (freshU b E X) - 1)).trace‖ +
      (‖matrixExpect (freshLaw W b) (freshU b E X) - 1‖ * (resolventWeight Q a).trace.re *
          (2 * (Cf * (Real.sqrt W)⁻¹) * (resolventWeight Q a).trace.re +
            ‖matrixExpect (freshLaw W b) (freshU b E X) - 1‖ * (resolventWeight Q a).trace.re) +
        ‖(∫ ω, (resolventWeight Q a * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b) -
          (((transportD0 b E / W : ℝ)) : ℂ) * (resolventWeight Q a * resolventWeight Q a).trace‖ +
        ‖(∫ ω, (resolventWeight Q a * freshU0 b E X ω * resolventWeight Q a *
            freshU0 b E X ω).trace ∂freshLaw W b) -
          (((transportD0 b E / W : ℝ)) : ℂ) * (resolventWeight Q a).trace ^ 2‖) +
      a * (qv / W) * |(∫ ω, (freshC b E X ω).trace.re ∂freshLaw W b) / W - dStar b|) :
    |stepDefect W b E qv a X Q| ≤
      domConst K Kq Kf Cw Cf Cc Ci CA * pastWeight W b E s X Q ^ 9 * ((Real.sqrt W)⁻¹) ^ 3 := by
  obtain ⟨ha0', haK⟩ := ha
  have hK0 : 0 < K := by linarith
  have ha0 : 0 ≤ a := le_trans (inv_nonneg.mpr hK0.le) ha0'
  obtain ⟨hqv0, hqvK⟩ := hqv
  set w := (Real.sqrt W)⁻¹ with hwdef
  have hsW : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW
  have hsW0 : 0 < Real.sqrt W := by linarith
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ hsW
  have hW0 : (0 : ℝ) < W := by linarith
  have hw2 : w ^ 2 = (W : ℝ)⁻¹ := by
    rw [hwdef, inv_pow, Real.sq_sqrt hW0.le]
  have hw4 : w ^ 4 = ((W : ℝ)⁻¹) ^ 2 := by
    rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, hw2]
  set Λ := pastWeight W b E s X Q with hΛdef
  set γ := Q.trace.re with hγdef
  set δ₀ := jetDistance0 b E X with hδ₀
  set δ₁ := jetDistance1 b E s X with hδ₁
  set f := passiveF b E X with hfdef
  set Z := ‖(Q * f).trace‖ with hZ
  set S' := hsSandwich Q f with hS'
  have hγ0 : 0 ≤ γ := trace_re_nonneg hQ
  have hδ0 : 0 ≤ δ₀ := norm_nonneg _
  have hδ10 : 0 ≤ δ₁ := norm_nonneg _
  have hZ0 : 0 ≤ Z := norm_nonneg _
  have hS0 : 0 ≤ S' := hsSandwich_nonneg _ _
  have hΛe : Λ = 1 + γ + W * (δ₀ + δ₁) + Real.sqrt W * (Z + S') := rfl
  have hWδ : 0 ≤ (W : ℝ) * (δ₀ + δ₁) := by positivity
  have hsZ : 0 ≤ Real.sqrt W * (Z + S') := by positivity
  have hΛ1 : 1 ≤ Λ := by rw [hΛe]; linarith
  have hγΛ : γ ≤ Λ := by rw [hΛe]; linarith
  have hδΛ : δ₀ ≤ Λ * w ^ 2 := by
    rw [hw2, ← div_eq_mul_inv, le_div_iff₀ hW0]
    have : (W : ℝ) * δ₀ ≤ W * (δ₀ + δ₁) := mul_le_mul_of_nonneg_left (by linarith) hW0.le
    rw [hΛe]; linarith
  have hδ1Λ : δ₁ ≤ Λ * w ^ 2 := by
    rw [hw2, ← div_eq_mul_inv, le_div_iff₀ hW0]
    have : (W : ℝ) * δ₁ ≤ W * (δ₀ + δ₁) := mul_le_mul_of_nonneg_left (by linarith) hW0.le
    rw [hΛe]; linarith
  have hZΛ : Z ≤ Λ * w := by
    rw [hwdef, ← div_eq_mul_inv, le_div_iff₀ hsW0]
    have : Real.sqrt W * Z ≤ Real.sqrt W * (Z + S') := mul_le_mul_of_nonneg_left (by linarith)
      hsW0.le
    rw [hΛe]; linarith
  have hSΛ : S' ≤ Λ * w := by
    rw [hwdef, ← div_eq_mul_inv, le_div_iff₀ hsW0]
    have : Real.sqrt W * S' ≤ Real.sqrt W * (Z + S') := mul_le_mul_of_nonneg_left (by linarith)
      hsW0.le
    rw [hΛe]; linarith
  -- weights
  set A := resolventWeight Q a with hAdef
  have hApsd : A.PosSemidef := resolventWeight_posSemidef hQ ha0
  set TA := A.trace.re with hTAdef
  have hTA0 : 0 ≤ TA := trace_re_nonneg hApsd
  have hTA : TA ≤ K * Λ := (re_trace_resolventWeight_le hQ ha0).trans
    (mul_le_mul_nn ha0 haK hγ0 hγΛ)
  set tAf := ‖(A * f).trace‖ with htAf
  have htAf0 : 0 ≤ tAf := norm_nonneg _
  have hΛ0 : 0 ≤ Λ := by linarith
  have htAfb : tAf ≤ 2 * K ^ 2 * Λ ^ 2 * w := by
    have h := norm_trace_weight_mul_le hQ ha0 f
    have h1 : a * Z ≤ K * (Λ * w) := mul_le_mul_nn ha0 haK hZ0 hZΛ
    have h2 : a ^ 2 * γ * S' ≤ K ^ 2 * Λ * (Λ * w) :=
      mul_le_mul_nn (by positivity) (mul_le_mul_nn (sq_nonneg a) (pow_le_pow_left₀ ha0 haK 2)
        hγ0 hγΛ) hS0 hSΛ
    have h3 : K * (Λ * w) ≤ K ^ 2 * Λ ^ 2 * w := by
      have hKK : K ≤ K ^ 2 := le_self_pow₀ hK (by norm_num)
      have hΛΛ : Λ ≤ Λ ^ 2 := le_self_pow₀ hΛ1 (by norm_num)
      have := mul_le_mul_nn hK0.le hKK (by positivity) (mul_le_mul_of_nonneg_right hΛΛ hw0)
      linarith
    have h4 : K ^ 2 * Λ * (Λ * w) = K ^ 2 * Λ ^ 2 * w := by ring
    linarith
  set sAf := (A * f * A * fᴴ).trace.re with hsAf
  have hsAf0 : 0 ≤ sAf := by
    rw [hsAf, trace_sandwich_eq_sum hApsd.1, Complex.ofReal_re]; exact sandwichSum_nonneg hApsd f
  have hsAfb : sAf ≤ K ^ 2 * Λ ^ 2 * w ^ 2 := by
    have h := trace_weight_sandwich_le hQ ha0 f
    have hS2 : (Q * f * Q * fᴴ).trace.re = S' ^ 2 := by
      rw [hS', hsSandwich_eq_sqrt hQ.1, Real.sq_sqrt (sandwichSum_nonneg hQ f),
        trace_sandwich_eq_sum hQ.1, Complex.ofReal_re]
    rw [hS2] at h
    have h1 : S' ^ 2 ≤ (Λ * w) ^ 2 := pow_le_pow_left₀ hS0 hSΛ 2
    have h2 : a ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ ha0 haK 2
    have := mul_le_mul_nn (sq_nonneg a) h2 (sq_nonneg _) h1
    calc sAf ≤ a ^ 2 * S' ^ 2 := h
      _ ≤ K ^ 2 * (Λ * w) ^ 2 := this
      _ = _ := by ring
  -- the mean
  set M := matrixExpect (freshLaw W b) (freshU b E X) - 1 with hMdef
  set Rem := M - Ω • f - (starRingEnd ℂ) Ω • fᴴ with hRemdef
  have hRemn : ‖Rem‖ ≤ Cw * (δ₀ ^ 2 + w ^ 4) := by rw [hw4]; exact hRem
  have hΩb : ‖Ω‖ ≤ 2 * Cw * Λ * w ^ 2 := by
    have h1 : δ₀ + w ^ 4 ≤ 2 * Λ * w ^ 2 := by
      have : w ^ 4 ≤ w ^ 2 := pow_le_pow_of_le_one hw0 hw1 (by norm_num)
      have : w ^ 2 ≤ Λ * w ^ 2 := by
        have := mul_le_mul_of_nonneg_right hΛ1 (sq_nonneg w); linarith
      linarith
    have := mul_le_mul_of_nonneg_left h1 hCw
    rw [hw4] at this
    linarith
  have hMsplit : M = Ω • f + (starRingEnd ℂ) Ω • fᴴ + Rem := by rw [hRemdef]; abel
  have hfH : ‖fᴴ‖ = ‖f‖ := l2_opNorm_conjTranspose _
  have hMn : ‖M‖ ≤ (4 * Cw * Kf + 2 * Cw) * Λ ^ 2 * w ^ 2 := by
    have h1 : ‖M‖ ≤ ‖Ω‖ * ‖f‖ + ‖Ω‖ * ‖f‖ + ‖Rem‖ := by
      rw [hMsplit]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        (norm_smul_le _ _) ((norm_smul_le _ _).trans (le_of_eq ?_)))) le_rfl)
      rw [Complex.norm_conj, hfH]
    have h2 : ‖Ω‖ * ‖f‖ ≤ (2 * Cw * Λ * w ^ 2) * Kf :=
      mul_le_mul_nn (norm_nonneg _) hΩb (norm_nonneg _) hKf
    have h3 : Cw * (δ₀ ^ 2 + w ^ 4) ≤ 2 * Cw * Λ ^ 2 * w ^ 4 := by
      have e1 : δ₀ ^ 2 ≤ (Λ * w ^ 2) ^ 2 := pow_le_pow_left₀ hδ0 hδΛ 2
      have e2 : w ^ 4 ≤ Λ ^ 2 * w ^ 4 := by
        have := mul_le_mul_of_nonneg_right (one_le_pow₀ hΛ1 : (1 : ℝ) ≤ Λ ^ 2)
          (pow_nonneg hw0 4); linarith
      have := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hCw
      calc Cw * (δ₀ ^ 2 + w ^ 4) ≤ Cw * ((Λ * w ^ 2) ^ 2 + Λ ^ 2 * w ^ 4) := this
        _ = _ := by ring
    have h4 : 2 * Cw * Λ ^ 2 * w ^ 4 ≤ 2 * Cw * Λ ^ 2 * w ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hw0 hw1 (by norm_num)) (by positivity)
    have h5 : (2 * Cw * Λ * w ^ 2) * Kf ≤ 2 * Cw * Kf * Λ ^ 2 * w ^ 2 := by
      have hΛΛ : Λ ≤ Λ ^ 2 := le_self_pow₀ hΛ1 (by norm_num)
      have := mul_le_mul_of_nonneg_left hΛΛ (by positivity : 0 ≤ 2 * Cw * Kf * w ^ 2)
      calc (2 * Cw * Λ * w ^ 2) * Kf = 2 * Cw * Kf * w ^ 2 * Λ := by ring
        _ ≤ 2 * Cw * Kf * w ^ 2 * Λ ^ 2 := this
        _ = _ := by ring
    have e : (4 * Cw * Kf + 2 * Cw) * Λ ^ 2 * w ^ 2 =
        2 * (2 * Cw * Kf * Λ ^ 2 * w ^ 2) + 2 * Cw * Λ ^ 2 * w ^ 2 := by ring
    linarith
  have hAM : ‖(A * M).trace‖ ≤ 2 * ‖Ω‖ * tAf + Cw * (δ₀ ^ 2 + w ^ 4) * TA := by
    rw [hMsplit, Matrix.mul_add, Matrix.mul_add, trace_add, trace_add, Matrix.mul_smul,
      Matrix.mul_smul, trace_smul, trace_smul]
    have h1 : ‖Ω • (A * f).trace‖ = ‖Ω‖ * tAf := by rw [norm_smul]
    have h2 : ‖(starRingEnd ℂ) Ω • (A * fᴴ).trace‖ = ‖Ω‖ * tAf := by
      rw [norm_smul, Complex.norm_conj, DetClockCov.norm_trace_mul_conjTranspose hApsd.1]
    have h3 : ‖(A * Rem).trace‖ ≤ Cw * (δ₀ ^ 2 + w ^ 4) * TA :=
      (norm_trace_mul_le hApsd Rem).trans (mul_le_mul_of_nonneg_right hRemn hTA0)
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) h3).trans ?_
    rw [h1, h2]; linarith
  -- covariance and injection errors, in `w`
  obtain ⟨hc1, hc2⟩ := hcov
  have hWinv : (W : ℝ)⁻¹ = w ^ 2 := hw2.symm
  have hcov1' : ‖(∫ ω, (A * freshU0 b E X ω * A * freshU0 b E X ω).trace ∂freshLaw W b) -
      (((transportD0 b E / W : ℝ)) : ℂ) * A.trace ^ 2‖ ≤
      Cc * (tAf ^ 2 * w ^ 2 + (w ^ 4 + w ^ 2 * (δ₀ + δ₁)) * TA ^ 2) := by
    refine hc1.trans (le_of_eq ?_)
    rw [div_eq_mul_inv _ (W : ℝ), hWinv]; ring
  have hcov2' : ‖(∫ ω, (A * freshU0 b E X ω).trace ^ 2 ∂freshLaw W b) -
      (((transportD0 b E / W : ℝ)) : ℂ) * (A * A).trace‖ ≤
      Cc * (sAf * w ^ 2 + (w ^ 4 + w ^ 2 * (δ₀ + δ₁)) * TA ^ 2) := by
    refine hc2.trans (le_of_eq ?_)
    rw [div_eq_mul_inv _ (W : ℝ), hWinv]; ring
  set injE := |(∫ ω, (freshC b E X ω).trace.re ∂freshLaw W b) / W - dStar b| with hinjE
  have hinj' : injE ≤ Ci * (δ₀ + w ^ 4) := by rw [hw4]; exact hinj
  -- the final arithmetic
  have hκ0 : 0 ≤ qv / (W : ℝ) ^ 2 := by positivity
  have hκ : qv / (W : ℝ) ^ 2 ≤ Kq * w ^ 4 := by
    rw [hw4, div_eq_mul_inv, inv_pow]
    exact mul_le_mul_of_nonneg_right hqvK (by positivity)
  have hκmβ : qv / (W : ℝ) ^ 2 * ((W : ℝ) * CA ^ 2) ≤ Kq * CA ^ 2 * w ^ 2 := by
    have e : qv / (W : ℝ) ^ 2 * ((W : ℝ) * CA ^ 2) = qv * CA ^ 2 * w ^ 2 := by
      rw [hw2]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqvK (sq_nonneg _))
      (sq_nonneg _)
  have hqvW : qv / (W : ℝ) = qv * w ^ 2 := by rw [hw2, div_eq_mul_inv]
  have key := numeric_domain (Λ := Λ) (w := w) (Kf := Kf) (Cw := Cw) (Cf := Cf) (Cc := Cc)
    (Ci := Ci) (CA := CA) (a := a) (qv := qv) (γ := γ) (δ₀ := δ₀) (δ₁ := δ₁) (TA := TA)
    (tAf := tAf) (sAf := sAf) (nΩ := ‖Ω‖) (nM := ‖M‖) (c := Cf * w) (mβ := (W : ℝ) * CA ^ 2)
    (κ := qv / (W : ℝ) ^ 2) hΛ1 hw0 hw1 hK hKq hKf0 hCw hCf hCc hCi hCA ha0 haK hqv0 hqvK hγ0 hγΛ
    hδ0 hδΛ hδ10 hδ1Λ hTA0 hTA htAf0 htAfb hsAf0 hsAfb (norm_nonneg _) hΩb (norm_nonneg _) hMn
    rfl hκ0 hκ (by positivity) hκmβ hAM hcov2' hcov1' (abs_nonneg _) hinj'
  rw [hqvW] at hdec
  unfold domConst
  exact hdec.trans key

theorem transportD0_pos {b E : ℝ} (hb0 : 0 < b) (hE0 : -2 < E) (hE1 : E < 2) :
    0 < transportD0 b E := by
  unfold transportD0
  have : 0 < 4 - E ^ 2 := by nlinarith
  positivity

theorem dStar_pos {b : ℝ} (hb1 : b < 1) : 0 < dStar b := by
  unfold dStar; have : 0 < 1 - b := by linarith
  positivity

/-- **The trivial bound** (used off the scalar domain):
`|stepDefect| ≤ 2 + W⁻¹(D₀ (Tr A_a)² + d q a)`. -/
theorem stepDefect_crude {b E qv a : ℝ} {X Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (ha : 0 ≤ a) (hqv : 0 ≤ qv) (hD : 0 ≤ transportD0 b E) (hd : 0 ≤ dStar b) :
    |stepDefect W b E qv a X Q| ≤
      2 + (W : ℝ)⁻¹ * (transportD0 b E * (resolventWeight Q a).trace.re ^ 2 +
        dStar b * qv * a) := by
  have hF0 := detLaplace_pos hQ ha
  have hF1 := detLaplace_le_one hQ ha
  have hP : ∀ ω, ((freshL b E X ω)ᴴ * Q * freshL b E X ω +
      ((qv / (W : ℝ) ^ 2 : ℝ) : ℂ) • freshC b E X ω).PosSemidef := by
    intro ω
    have h1 := hQ.conjTranspose_mul_mul_same (freshL b E X ω)
    refine PosSemidef.add (by simpa [Matrix.mul_assoc] using h1) ((freshC_posSemidef b E X ω).smul ?_)
    exact Complex.zero_le_real.mpr (by positivity)
  have hIF : |∫ ω, detLaplace ((freshL b E X ω)ᴴ * Q * freshL b E X ω +
      ((qv / (W : ℝ) ^ 2 : ℝ) : ℂ) • freshC b E X ω) a ∂freshLaw W b| ≤ 1 := by
    have h := norm_integral_le_of_norm_le_const (μ := freshLaw W b) (C := 1)
      (f := fun ω => detLaplace ((freshL b E X ω)ᴴ * Q * freshL b E X ω +
        ((qv / (W : ℝ) ^ 2 : ℝ) : ℂ) • freshC b E X ω) a) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (detLaplace_pos (hP ω) ha)]
        exact detLaplace_le_one (hP ω) ha)
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
    exact h
  have hTA0 := re_trace_resolventWeight_nonneg hQ ha
  have hA2 := trace_weight_sq_le hQ ha
  have hA20 : 0 ≤ ((resolventWeight Q a) ^ 2).trace.re := by
    rw [trace_resolventWeight_sq_eq_sum hQ ha, Complex.ofReal_re]; positivity
  set T := (resolventWeight Q a).trace.re
  set T2 := ((resolventWeight Q a) ^ 2).trace.re
  have hG : |transportD0 b E / 2 * (detLaplace Q a * (T ^ 2 + T2)) -
      dStar b * qv * a * detLaplace Q a| ≤ transportD0 b E * T ^ 2 + dStar b * qv * a := by
    have h1 : 0 ≤ transportD0 b E / 2 * (detLaplace Q a * (T ^ 2 + T2)) := by positivity
    have h2 : 0 ≤ dStar b * qv * a * detLaplace Q a := by positivity
    have h3 : transportD0 b E / 2 * (detLaplace Q a * (T ^ 2 + T2)) ≤ transportD0 b E * T ^ 2 := by
      have : detLaplace Q a * (T ^ 2 + T2) ≤ 1 * (2 * T ^ 2) :=
        mul_le_mul hF1 (by linarith) (by positivity) zero_le_one
      have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ transportD0 b E / 2)
      linarith
    have h4 : dStar b * qv * a * detLaplace Q a ≤ dStar b * qv * a := by
      have := mul_le_mul_of_nonneg_left hF1 (by positivity : 0 ≤ dStar b * qv * a)
      linarith
    rw [abs_le]; constructor <;> linarith
  unfold stepDefect
  have hW0 : 0 ≤ (W : ℝ)⁻¹ := by positivity
  have e := mul_le_mul_of_nonneg_left hG hW0
  have habs := abs_mul (W : ℝ)⁻¹ (transportD0 b E / 2 * (detLaplace Q a * (T ^ 2 + T2)) -
    dStar b * qv * a * detLaplace Q a)
  rw [abs_of_nonneg hW0] at habs
  have := abs_sub (∫ ω, detLaplace ((freshL b E X ω)ᴴ * Q * freshL b E X ω +
      ((qv / (W : ℝ) ^ 2 : ℝ) : ℂ) • freshC b E X ω) a ∂freshLaw W b - detLaplace Q a)
    ((W : ℝ)⁻¹ * (transportD0 b E / 2 * (detLaplace Q a * (T ^ 2 + T2)) -
      dStar b * qv * a * detLaplace Q a))
  have := abs_sub (∫ ω, detLaplace ((freshL b E X ω)ᴴ * Q * freshL b E X ω +
      ((qv / (W : ℝ) ^ 2 : ℝ) : ℂ) • freshC b E X ω) a ∂freshLaw W b) (detLaplace Q a)
  rw [abs_of_pos hF0] at this
  linarith

theorem le_max_mul {C x y : ℝ} (hx : 0 ≤ x) (h : y ≤ C * x) : y ≤ max C 0 * x :=
  h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx)

/-!
## 6. The one-step bound
-/

/-- **The one-step bound** (see the module docstring). -/
theorem stepDefect_le (hPSM : PassiveSourceMixingContract) (hPC : PassiveCovarianceContract)
    (hGA : GaussianAbsorptionContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract)
    {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) {s : ℂ}
    (hs : IsStationaryJet b E s) {K Kq : ℝ} (hK : 1 ≤ K) (hKq : 0 ≤ Kq) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      X.IsHermitian → ∀ Q : Matrix (Fin W) (Fin W) ℂ, Q.PosSemidef →
        ∀ a ∈ Set.Icc K⁻¹ K, ∀ qv ∈ Set.Icc 0 Kq,
          |stepDefect W b E qv a X Q| ≤
            C * pastWeight W b E s X Q ^ 9 * ((Real.sqrt W)⁻¹) ^ 3 := by
  have hη := DetClockInj.etaZ_pos (by linarith : b < 1) hE0 hE1
  have hz : 0 < (boundaryZ b E).im := hη
  obtain ⟨Cw, dw, Ww, hdw, hward⟩ := wardMean_of hGA hWC hb0 hb1 hE0 hE1
  obtain ⟨Cf, Wf, hfl⟩ := hPSM.oneStepFluctuation b hb0 hb1 E hE0 hE1 3 (by norm_num)
  obtain ⟨Cc, Wc, hcov⟩ := DetClockCov.covTraceSquare_of hPC hPSM hb0 hb1 hE0 hE1 hs
  obtain ⟨Ci, Wi, hinj⟩ := DetClockInj.injectionMean_of hGA hb0 hb1 hE0 hE1
  obtain ⟨ε₁, CA, hε₁, hCA, habs'⟩ := hGA b hb0 hb1 (etaZ b E) ‖boundaryZ b E‖ hη
  set Kf := (boundaryZ b E).im⁻¹ + ‖cZero b E‖ with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  have hD := (transportD0_pos hb0 hE0 hE1).le
  have hd := (dStar_pos (by linarith : b < 1)).le
  set Cdom := domConst K Kq Kf (max Cw 0) (max Cf 0) (max Cc 0) (max Ci 0) CA with hCdom
  set Coff := (2 + transportD0 b E * K ^ 2 + dStar b * Kq * K) / dw ^ 2 with hCoff
  have hK0 : 0 ≤ K := by linarith
  have hCdom0 : 0 ≤ Cdom := domConst_nonneg hK0 hKq hKf0 (le_max_right _ _) (le_max_right _ _)
    (le_max_right _ _) (le_max_right _ _)
  have hCoff0 : 0 ≤ Coff := by positivity
  refine ⟨Cdom + Coff, max (max (max Ww Wf) (max Wc Wi)) (max ⌈6 / ε₁⌉₊ 1),
    by positivity, fun W hWW X hX Q hQ a ha qv hqv => ?_⟩
  have hWw : Ww ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hWW
  have hWf : Wf ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hWW
  have hWc : Wc ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hWW
  have hWi : Wi ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hWW
  have hWε : ⌈6 / ε₁⌉₊ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hWW
  have hWpos : 0 < W := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) hWW))
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hWpos
  have hW0 : (0 : ℝ) < W := by linarith
  have h6W : (6 : ℝ) ≤ ε₁ * W := by
    have h1 : 6 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWε)
    rw [div_le_iff₀ hε₁] at h1; linarith
  obtain ⟨ha0', haK⟩ := ha
  have ha0 : 0 ≤ a := le_trans (inv_nonneg.mpr hK0) ha0'
  obtain ⟨hqv0, hqvK⟩ := hqv
  set w := (Real.sqrt W)⁻¹ with hwdef
  have hsW : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW1
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ hsW
  have hw2 : w ^ 2 = (W : ℝ)⁻¹ := by rw [hwdef, inv_pow, Real.sq_sqrt hW0.le]
  -- the fresh layer
  have hXl := CavityMeanProb.cavityLift_isHermitian hX
  obtain ⟨_hinv, hmom⟩ := habs' W hWpos LayerShape.oneBlockOnePort (cavityLift X) hXl E
    (boundaryZ b E) le_rfl le_rfl
  have hG6 : eLpNorm (fun ω => ‖freshLayer b E X ω‖) (ENNReal.ofReal (2 * 3)) (freshLaw W b) ≤
      ENNReal.ofReal CA := by
    rw [show (2 : ℝ) * 3 = 6 by norm_num]; exact hmom 6 (by norm_num) h6W
  have hG2 : Integrable (fun ω => ‖freshLayer b E X ω‖ ^ 2) (freshLaw W b) :=
    BlockBand.Layers.meq_sq_integrable_of_eLpNorm (hmom 2 (by norm_num) (by linarith))
  have hsq := condSq_le (ν := freshLaw W b) (p := 3) (by norm_num) hCA.le hG6
  have hCm : Measurable (fun ω => freshC b E X ω) :=
    (meas_freshC (W := W) b E).comp (f := fun ω => (X, ω)) (measurable_const.prodMk measurable_id)
  have hβ : eLpNorm (fun ω => (freshC b E X ω).trace.re) (ENNReal.ofReal 3) (freshLaw W b) ≤
      ENNReal.ofReal ((W : ℝ) * CA ^ 2) := by
    have h1 : eLpNorm (fun ω => (freshC b E X ω).trace.re) (ENNReal.ofReal 3) (freshLaw W b) ≤
        eLpNorm (fun ω => (W : ℝ) * ‖freshLayer b E X ω‖ ^ 2) (ENNReal.ofReal 3) (freshLaw W b) :=
      eLpNorm_mono_real (Complex.measurable_re.comp (meas_trace hCm)).aestronglyMeasurable
        fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (trace_re_nonneg (freshC_posSemidef b E X ω))]
          exact trace_freshC_le b E X ω
    refine h1.trans ?_
    rw [eLpNorm_real_mul_le, abs_of_nonneg hW0.le, ENNReal.ofReal_mul hW0.le]
    gcongr
  have hCn : eLpNorm (fun ω => ‖freshC b E X ω‖) (ENNReal.ofReal 3) (freshLaw W b) ≤
      ENNReal.ofReal (CA ^ 2) := by
    refine le_trans (eLpNorm_mono_real (meas_freshC (W := W) b E |>.comp
      (f := fun ω => (X, ω)) (measurable_const.prodMk measurable_id)).norm.aestronglyMeasurable
      fun ω => ?_) hsq
    rw [Real.norm_eq_abs, abs_norm]; exact norm_freshC_le b E X ω
  have hUi := integrable_freshU_apply hG2
  have hfl3 : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (freshU b E X ω -
      matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal 3) (freshLaw W b) ≤
      ENNReal.ofReal (max Cf 0 * (Real.sqrt W)⁻¹ * vecNorm u * vecNorm v) := by
    intro u v
    refine (hfl W hWf X (passiveY_posSemidef hX) u v).1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hu : 0 ≤ vecNorm u := Real.sqrt_nonneg _
    have hv : 0 ≤ vecNorm v := Real.sqrt_nonneg _
    rw [div_eq_mul_inv]
    gcongr
    exact le_max_left _ _
  have hdec := stepDefect_decomp (b := b) (E := E) (qv := qv) (a := a) (X := X) hQ ha0 hqv0
    hWpos (c := max Cf 0 * (Real.sqrt W)⁻¹) (mβ := (W : ℝ) * CA ^ 2) (mC := CA ^ 2)
    (by positivity) (by positivity) (sq_nonneg _) hUi hfl3 hβ hCn
  by_cases hδ : jetDistance0 b E X ≤ dw
  · -- the scalar domain
    obtain ⟨Ω, hΩ, hRem⟩ := hward W hWw X hX hδ
    have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have hApsd := resolventWeight_posSemidef hQ ha0
    obtain ⟨hc1, hc2⟩ := hcov W hWc X hX (resolventWeight Q a) hApsd
    have hb1' : 0 ≤ (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
        (jetDistance0 b E X + jetDistance1 b E s X) := by
      have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
      positivity
    have hsA0 : 0 ≤ (resolventWeight Q a * passiveF b E X * resolventWeight Q a *
        (passiveF b E X)ᴴ).trace.re := by
      rw [trace_sandwich_eq_sum hApsd.1, Complex.ofReal_re]; exact sandwichSum_nonneg hApsd _
    have hcov' := And.intro
      (le_max_mul (add_nonneg (by positivity) (mul_nonneg hb1' (sq_nonneg _))) hc1)
      (le_max_mul (add_nonneg (div_nonneg hsA0 hW0.le) (mul_nonneg hb1' (sq_nonneg _))) hc2)
    refine (stepDefect_domain hW1 hQ hK hKq ⟨ha0', haK⟩ ⟨hqv0, hqvK⟩ (le_max_right _ _)
      (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) hCA.le hKf0
      (ClockMixingAlg.norm_passiveF_le b E hz hX) Ω (le_max_mul (by positivity) hΩ)
      (le_max_mul (by positivity) hRem) hcov'
      (le_max_mul (by positivity) (hinj W hWi X hX).2) hdec).trans ?_
    have hP0 : 0 ≤ pastWeight W b E s X Q ^ 9 * w ^ 3 := by
      have : 0 ≤ pastWeight W b E s X Q := by
        unfold pastWeight
        have h1 := trace_re_nonneg hQ
        have h2 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
        have h3 := hsSandwich_nonneg Q (passiveF b E X)
        have h4 : 0 ≤ (W : ℝ) * (jetDistance0 b E X + jetDistance1 b E s X) :=
          mul_nonneg hW0.le (add_nonneg hδ0 h2)
        have h5 : 0 ≤ Real.sqrt W * (‖(Q * passiveF b E X).trace‖ +
            hsSandwich Q (passiveF b E X)) := mul_nonneg (Real.sqrt_nonneg _)
          (add_nonneg (norm_nonneg _) h3)
        linarith
      positivity
    have := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCoff0 : Cdom ≤ Cdom + Coff) hP0
    calc Cdom * pastWeight W b E s X Q ^ 9 * w ^ 3 = Cdom * (pastWeight W b E s X Q ^ 9 * w ^ 3) :=
          by ring
      _ ≤ (Cdom + Coff) * (pastWeight W b E s X Q ^ 9 * w ^ 3) := this
      _ = _ := by ring
  · -- off the scalar domain
    push Not at hδ
    have hcr := stepDefect_crude (X := X) hQ ha0 hqv0 hD hd (b := b) (E := E) (qv := qv) (W := W)
    set Λ := pastWeight W b E s X Q with hΛ
    have hγ0 := trace_re_nonneg hQ
    have hδ10 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    have hΛe : Λ = 1 + Q.trace.re + W * (jetDistance0 b E X + jetDistance1 b E s X) +
        Real.sqrt W * (‖(Q * passiveF b E X).trace‖ + hsSandwich Q (passiveF b E X)) := rfl
    have hsZ : 0 ≤ Real.sqrt W * (‖(Q * passiveF b E X).trace‖ + hsSandwich Q (passiveF b E X)) :=
      by have := hsSandwich_nonneg Q (passiveF b E X); positivity
    have hWδ : 0 ≤ (W : ℝ) * (jetDistance0 b E X + jetDistance1 b E s X) := by
      have : 0 ≤ jetDistance0 b E X := norm_nonneg _
      positivity
    have hΛ1 : 1 ≤ Λ := by rw [hΛe]; linarith
    have hγΛ : Q.trace.re ≤ Λ := by rw [hΛe]; linarith
    have hδΛ : jetDistance0 b E X ≤ Λ * w ^ 2 := by
      rw [hw2, ← div_eq_mul_inv, le_div_iff₀ hW0]
      have : (W : ℝ) * jetDistance0 b E X ≤ W * (jetDistance0 b E X + jetDistance1 b E s X) :=
        mul_le_mul_of_nonneg_left (by linarith) hW0.le
      rw [hΛe]; linarith
    have hTA := (re_trace_resolventWeight_le hQ ha0).trans (mul_le_mul_nn ha0 haK hγ0 hγΛ)
    have hTA0 := re_trace_resolventWeight_nonneg hQ ha0
    have hTA2 : (resolventWeight Q a).trace.re ^ 2 ≤ (K * Λ) ^ 2 := pow_le_pow_left₀ hTA0 hTA 2
    have hΛ0 : 0 ≤ Λ := by linarith
    have hΛ2 : (1 : ℝ) ≤ Λ ^ 2 := one_le_pow₀ hΛ1
    have hc1 : |stepDefect W b E qv a X Q| ≤ (2 + transportD0 b E * K ^ 2 + dStar b * Kq * K) *
        Λ ^ 2 := by
      refine hcr.trans ?_
      have hWi1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
      have h1 : transportD0 b E * (resolventWeight Q a).trace.re ^ 2 + dStar b * qv * a ≤
          (transportD0 b E * K ^ 2 + dStar b * Kq * K) * Λ ^ 2 := by
        have e1 : transportD0 b E * (resolventWeight Q a).trace.re ^ 2 ≤
            transportD0 b E * K ^ 2 * Λ ^ 2 := by
          have := mul_le_mul_of_nonneg_left hTA2 hD
          calc _ ≤ transportD0 b E * (K * Λ) ^ 2 := this
            _ = _ := by ring
        have e2 : dStar b * qv * a ≤ dStar b * Kq * K * Λ ^ 2 := by
          have h3 : dStar b * qv * a ≤ dStar b * Kq * K :=
            mul_le_mul_nn (mul_nonneg hd hqv0) (mul_le_mul_of_nonneg_left hqvK hd) ha0 haK
          have h4 := mul_le_mul_of_nonneg_left hΛ2 (by positivity : 0 ≤ dStar b * Kq * K)
          linarith
        have e : (transportD0 b E * K ^ 2 + dStar b * Kq * K) * Λ ^ 2 =
            transportD0 b E * K ^ 2 * Λ ^ 2 + dStar b * Kq * K * Λ ^ 2 := by ring
        linarith
      have h2 := mul_le_mul_nn (by positivity) hWi1 (by positivity) h1
      have h3 : (2 : ℝ) ≤ 2 * Λ ^ 2 := by linarith
      have e : (2 + transportD0 b E * K ^ 2 + dStar b * Kq * K) * Λ ^ 2 =
          2 * Λ ^ 2 + (transportD0 b E * K ^ 2 + dStar b * Kq * K) * Λ ^ 2 := by ring
      linarith
    have hratio : 1 ≤ (Λ * w ^ 2 / dw) ^ 2 := by
      have : 1 ≤ Λ * w ^ 2 / dw := by rw [le_div_iff₀ hdw]; linarith
      exact one_le_pow₀ this
    have hc2 : |stepDefect W b E qv a X Q| ≤ Coff * Λ ^ 4 * w ^ 4 := by
      have h0 : 0 ≤ (2 + transportD0 b E * K ^ 2 + dStar b * Kq * K) * Λ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hratio h0
      calc |stepDefect W b E qv a X Q| ≤ (2 + transportD0 b E * K ^ 2 + dStar b * Kq * K) *
            Λ ^ 2 * 1 := by rw [mul_one]; exact hc1
        _ ≤ (2 + transportD0 b E * K ^ 2 + dStar b * Kq * K) * Λ ^ 2 * (Λ * w ^ 2 / dw) ^ 2 :=
            this
        _ = Coff * Λ ^ 4 * w ^ 4 := by rw [hCoff]; field_simp
    have hc3 := le_mono_bound (k := 4) (l := 4) hCoff0 hΛ1 hw0 hw1 (by norm_num) (by norm_num) hc2
    have hP0 : 0 ≤ Λ ^ 9 * w ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCdom0 : Coff ≤ Cdom + Coff) hP0
    calc |stepDefect W b E qv a X Q| ≤ Coff * Λ ^ 9 * w ^ 3 := hc3
      _ = Coff * (Λ ^ 9 * w ^ 3) := by ring
      _ ≤ (Cdom + Coff) * (Λ ^ 9 * w ^ 3) := this
      _ = _ := by ring

end DetClockProof

end BlockBand.Endpoints.Clock
