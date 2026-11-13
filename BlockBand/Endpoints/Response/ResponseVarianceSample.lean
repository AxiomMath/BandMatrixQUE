module

public import BlockBand.Endpoints.Response.ResponseVarianceLead

/-!
# The signed response against the Gaussian ratio, sample by sample

* `rv_sandwich`: `-A ⪯ B_q ⪯ A` for `|q| ≤ 1`.
* `rv_signedDeriv_le_ratio` (from `RvSignedTraceBound` and `RvGaussianVarianceLower`):
  `|∂_q(F_L+F_R)| ≤ C₁ (1 + √g) Tr A (E_h|h*B_qh/h*Ah|²)^{1/2}`.
* `rv_ratio_sq_le`: `rvRatio² ≤ 3 c₀² + 3 ε² + 3 a_port` for the cosine source, `c₀ = rvLeadCos`
  the cosine coefficient of the lead profile, `a_port` the port fraction, `ε` a bound for the
  source-location change `|q_m((r-i)/W) - cos(2πm(i+2)/n)|`; and `rv_cosine_grid_le` gives
  `ε = 2π|m|(|r/(τW) - r/n| + 1/n)` for `r = n - 3`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
  BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal ComplexOrder

variable {b e : ℝ} {W r : ℕ}

/-!
### Quadratic forms
-/

theorem rv_leadFrame_eq (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    rvLeadFrame b e W r ω = leadResponse b e W r ω := by
  ext x a
  simp [rvLeadFrame, leadResponse, leadInclusion, mul_apply, Fintype.sum_sum_type]

theorem rv_quadForm_conj_diagonal {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix κ ι ℂ) (d : κ → ℝ) (h : ι → ℂ) :
    quadForm (Uᴴ * diagonal (fun x => (d x : ℂ)) * U) h = ∑ x, d x * ‖(U *ᵥ h) x‖ ^ 2 := by
  rw [quadForm, ← mulVec_mulVec, ← mulVec_mulVec, star_dotProduct_mulVec_eq,
    conjTranspose_conjTranspose]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_left_comm, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The real diagonal of `sourceDiag`. -/
def rvSourceWeight (W r : ℕ) (q : ℝ → ℝ) : FullSite W r → ℝ :=
  Sum.elim (fun s => q (((r - s.1.val : ℕ) : ℝ) / W) / (W : ℝ) ^ 2) fun _ => 0

theorem rv_sourceDiag_eq (W r : ℕ) (q : ℝ → ℝ) :
    sourceDiag W r q = diagonal (fun x => ((rvSourceWeight W r q x : ℝ) : ℂ)) := by
  rw [sourceDiag]
  congr 1
  funext x
  rcases x with s | a <;> simp [rvSourceWeight]

theorem rv_leadClock_eq (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    rvLeadClock b e W r ω = (rvLeadFrame b e W r ω)ᴴ *
      diagonal (fun _ : FullSite W r => ((((W : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) * rvLeadFrame b e W r ω := by
  rw [rvLeadClock, Matrix.mul_assoc, ← smul_eq_diagonal_mul, Matrix.mul_smul]

theorem rv_quadForm_sourceGram (b e : ℝ) (W r : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) :
    quadForm (rvSourceGram b e W r q ω) h = ((W : ℝ) ^ 2)⁻¹ *
      ∑ i : Fin r, q (((r - i.val : ℕ) : ℝ) / W) * leadPositionMass b e W r ω h (Sum.inl i) := by
  rw [rvSourceGram, rv_sourceDiag_eq, rv_quadForm_conj_diagonal, rv_leadFrame_eq,
    Fintype.sum_sum_type, Finset.mul_sum]
  simp only [rvSourceWeight, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero,
    add_zero, Fintype.sum_prod_type, leadPositionMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem rv_quadForm_leadClock (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) (h : Fin 2 × Fin W → ℂ) :
    quadForm (rvLeadClock b e W r ω) h = ((W : ℝ) ^ 2)⁻¹ * totalLeadMass b e W r (ω, h) := by
  rw [rv_leadClock_eq, rv_quadForm_conj_diagonal, rv_leadFrame_eq, ← Finset.mul_sum,
    totalLeadMass, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [leadPositionMass, Fintype.sum_prod_type]

/-- The source-weighted mass fraction `Σ_{i<r} q((r-i)/W) h*Y_ih / h*Y^{all}h`. -/
def rvRatio (q : ℝ → ℝ) (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  (∑ i : Fin r, q (((r - i.val : ℕ) : ℝ) / W) * leadPositionMass b e W r x.1 x.2 (Sum.inl i)) /
    totalLeadMass b e W r x

theorem rv_quadForm_ratio (hW : 0 < W) (q : ℝ → ℝ) (ω : GrowthPath W) (h : Fin 2 × Fin W → ℂ) :
    quadForm (rvSourceGram b e W r q ω) h / quadForm (rvLeadClock b e W r ω) h =
      rvRatio q b e W r (ω, h) := by
  have hW' : ((W : ℝ) ^ 2)⁻¹ ≠ 0 := by positivity
  rw [rv_quadForm_sourceGram, rv_quadForm_leadClock, rvRatio, mul_div_mul_left _ _ hW']

theorem rv_measurable_ratio_of (q : ℝ → ℝ) (b : ℝ) (W r : ℕ) {α : Type*} [MeasurableSpace α]
    {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)} (he : Measurable e)
    (hx : Measurable x) : Measurable (fun a => rvRatio q b (e a) W r (x a)) := by
  unfold rvRatio
  exact (Finset.measurable_sum _ fun i _ => measurable_const.mul
    (measurable_leadPositionMass_of b W r (Sum.inl i) he hx)).div
    (rv_measurable_totalLeadMass_of b W r he hx)

theorem rv_abs_ratio_le {q : ℝ → ℝ} (hq : ∀ t, |q t| ≤ 1) (b e : ℝ) (W r : ℕ)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : |rvRatio q b e W r x| ≤ 1 := by
  have htot := rv_totalLeadMass_nonneg b e W r x
  rw [rvRatio, abs_div, abs_of_nonneg htot]
  rcases htot.lt_or_eq with hlt | heq
  · rw [div_le_one hlt]
    calc |∑ i : Fin r, q (((r - i.val : ℕ) : ℝ) / W) * leadPositionMass b e W r x.1 x.2 (Sum.inl i)|
        ≤ ∑ i : Fin r, leadPositionMass b e W r x.1 x.2 (Sum.inl i) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [abs_mul, abs_of_nonneg (leadPositionMass_nonneg _ _ _ _ _)]
          exact mul_le_of_le_one_left (leadPositionMass_nonneg _ _ _ _ _) (hq _)
      _ ≤ totalLeadMass b e W r x := by
          rw [totalLeadMass_eq]
          exact le_add_of_nonneg_right (portLeadMass_nonneg _ _ _)
  · rw [← heq, div_zero]; exact zero_le_one

/-!
### The sandwich `-A ⪯ B_q ⪯ A`
-/

theorem rv_posSemidef_conj_diagonal {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix κ ι ℂ) {d : κ → ℝ} (hd : ∀ x, 0 ≤ d x) :
    (Uᴴ * diagonal (fun x => (d x : ℂ)) * U).PosSemidef := by
  refine PosSemidef.conjTranspose_mul_mul_same ?_ U
  rw [posSemidef_diagonal_iff]
  intro x
  exact_mod_cast hd x

theorem rv_sandwich (hW : 0 < W) {q : ℝ → ℝ} (hq : ∀ t, |q t| ≤ 1) (ω : GrowthPath W) :
    IsSandwichedOn (rvSourceGram b e W r q ω) (rvLeadClock b e W r ω) := by
  have hW2 : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
  have hd : ∀ (s : ℝ), ((s : ℝ) : ℂ) = (s : ℂ) := fun _ => rfl
  set U := rvLeadFrame b e W r ω
  have hB : rvSourceGram b e W r q ω =
      Uᴴ * diagonal (fun x => ((rvSourceWeight W r q x : ℝ) : ℂ)) * U := by
    rw [rvSourceGram, rv_sourceDiag_eq]
  have hA := rv_leadClock_eq b e W r ω
  refine ⟨?_, ?_, ?_⟩
  · rw [hB]
    refine isHermitian_conjTranspose_mul_mul U ?_
    rw [IsHermitian, diagonal_conjTranspose]
    congr 1
    funext x
    simp [Complex.conj_ofReal]
  · rw [hA, hB, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    have : (fun x : FullSite W r => ((((W : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) -
        ((rvSourceWeight W r q x : ℝ) : ℂ)) =
        fun x => ((((W : ℝ) ^ 2)⁻¹ - rvSourceWeight W r q x : ℝ) : ℂ) := by
      funext x; push_cast; ring
    rw [this]
    refine rv_posSemidef_conj_diagonal U fun x => ?_
    rcases x with s | a
    · simp only [rvSourceWeight, Sum.elim_inl]
      rw [sub_nonneg, div_eq_mul_inv, mul_comm]
      have := (abs_le.1 (hq (((r - s.1.val : ℕ) : ℝ) / W))).2
      nlinarith [inv_pos.2 hW2]
    · simp only [rvSourceWeight, Sum.elim_inr, sub_zero]
      positivity
  · rw [hA, hB, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    have : (fun x : FullSite W r => ((((W : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) +
        ((rvSourceWeight W r q x : ℝ) : ℂ)) =
        fun x => ((((W : ℝ) ^ 2)⁻¹ + rvSourceWeight W r q x : ℝ) : ℂ) := by
      funext x; push_cast; ring
    rw [this]
    refine rv_posSemidef_conj_diagonal U fun x => ?_
    rcases x with s | a
    · simp only [rvSourceWeight, Sum.elim_inl]
      rw [div_eq_mul_inv, mul_comm]
      have := (abs_le.1 (hq (((r - s.1.val : ℕ) : ℝ) / W))).1
      nlinarith [inv_pos.2 hW2]
    · simp only [rvSourceWeight, Sum.elim_inr, add_zero]
      positivity

theorem rv_leadClock_trace_nonneg (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    0 ≤ (rvLeadClock b e W r ω).trace.re := by
  rw [rvLeadClock, trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    trace_conjTranspose_mul_self_re_eq_hsSq]
  exact mul_nonneg (by positivity) (hsSq_nonneg _)

/-!
### The signed response against the Gaussian ratio
-/

/-- Sample-wise reduction to the Gaussian ratio: from the signed response trace bound with
constant `c` and the Gaussian variance lower bound with constant `c_G`, for one sample:
`|∂_q(F_L+F_R)| ≤ 4 max(x+y, c) √(2c_G) (1 + √g) Tr A (E_h ratio²)^{1/2}`. -/
theorem rv_signedDeriv_le_ratio {x y c cG : ℝ} (hc : 0 ≤ c) (hcG : 0 < cG) (hxy : 0 ≤ x + y)
    (hW : 0 < W) {q : ℝ → ℝ} {ω : GrowthPath W} (hη1 : etaZ b e ≤ 1)
    (hD : |rvSignedDeriv b e x y W r q ω| ≤ 4 * etaZ b e *
        ((x + y) * |(rvSourceGram b e W r q ω).trace.re| +
          c * Real.sqrt (rvConductance b e W r ω) * Real.sqrt (hsSq (rvSourceGram b e W r q ω))))
    (hG : (rvSourceGram b e W r q ω).trace.re ^ 2 + hsSq (rvSourceGram b e W r q ω) ≤
        cG * (rvLeadClock b e W r ω).trace.re ^ 2 *
          ∫ h, (quadForm (rvSourceGram b e W r q ω) h / quadForm (rvLeadClock b e W r ω) h) ^ 2
            ∂circularVectorLaw (Fin 2 × Fin W)) :
    |rvSignedDeriv b e x y W r q ω| ≤ 4 * max (x + y) c * Real.sqrt (2 * cG) *
      ((1 + Real.sqrt (rvConductance b e W r ω)) * (rvLeadClock b e W r ω).trace.re *
        Real.sqrt (∫ h, rvRatio q b e W r (ω, h) ^ 2 ∂circularVectorLaw (Fin 2 × Fin W))) := by
  have hI : (∫ h, (quadForm (rvSourceGram b e W r q ω) h / quadForm (rvLeadClock b e W r ω) h) ^ 2
      ∂circularVectorLaw (Fin 2 × Fin W)) =
      ∫ h, rvRatio q b e W r (ω, h) ^ 2 ∂circularVectorLaw (Fin 2 × Fin W) := by
    congr 1; funext h; rw [rv_quadForm_ratio hW]
  rw [hI] at hG
  set T := |(rvSourceGram b e W r q ω).trace.re|
  set H := Real.sqrt (hsSq (rvSourceGram b e W r q ω))
  set G := Real.sqrt (rvConductance b e W r ω)
  set A := (rvLeadClock b e W r ω).trace.re
  set I := ∫ h, rvRatio q b e W r (ω, h) ^ 2 ∂circularVectorLaw (Fin 2 × Fin W)
  set K := max (x + y) c
  have hT : 0 ≤ T := abs_nonneg _
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hA : 0 ≤ A := rv_leadClock_trace_nonneg b e W r ω
  have hI0 : 0 ≤ I := integral_nonneg fun h => sq_nonneg _
  have hK1 : x + y ≤ K := le_max_left _ _
  have hK2 : c ≤ K := le_max_right _ _
  have hK : 0 ≤ K := hxy.trans hK1
  have hH2 : H ^ 2 = hsSq (rvSourceGram b e W r q ω) := Real.sq_sqrt (hsSq_nonneg _)
  have hT2 : T ^ 2 = (rvSourceGram b e W r q ω).trace.re ^ 2 := sq_abs _
  -- `T + H ≤ √(2 c_G) A √I`
  have hTH : T + H ≤ Real.sqrt (2 * cG) * (A * Real.sqrt I) := by
    have hsq : (T + H) ^ 2 ≤ 2 * cG * A ^ 2 * I := by
      nlinarith [sq_nonneg (T - H)]
    have hR : Real.sqrt (2 * cG) * (A * Real.sqrt I) = Real.sqrt (2 * cG * A ^ 2 * I) := by
      rw [Real.sqrt_mul (by positivity) I, Real.sqrt_mul (by positivity) (A ^ 2),
        Real.sqrt_sq hA]
      ring
    rw [hR]
    exact Real.le_sqrt_of_sq_le hsq
  have hstep : (x + y) * T + c * G * H ≤ K * ((1 + G) * (T + H)) := by
    have h1 : (x + y) * T ≤ K * T := mul_le_mul_of_nonneg_right hK1 hT
    have h2 : c * G * H ≤ K * (G * H) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hK2 (mul_nonneg hG0 hH)
    nlinarith [mul_nonneg hK (mul_nonneg hG0 hT), mul_nonneg hK hH]
  have hS : 0 ≤ Real.sqrt (2 * cG) := Real.sqrt_nonneg _
  calc |rvSignedDeriv b e x y W r q ω| ≤ 4 * etaZ b e * ((x + y) * T + c * G * H) := hD
    _ ≤ 4 * 1 * (K * ((1 + G) * (T + H))) := by
        apply mul_le_mul (by linarith) hstep (by positivity) (by norm_num)
    _ ≤ 4 * 1 * (K * ((1 + G) * (Real.sqrt (2 * cG) * (A * Real.sqrt I)))) := by
        gcongr
    _ = 4 * K * Real.sqrt (2 * cG) * ((1 + G) * A * Real.sqrt I) := by ring

/-!
### The cosine source against the lead profile
-/

/-- Source-location change: for `r = n - 3`, `i < r`,
`|q_m((r-i)/W) - cos(2πm(i+2)/n)| ≤ 2π|m|(r |1/(τW) - 1/n| + 1/n)`. -/
theorem rv_cosine_grid_le (m : ℤ) {τ : ℝ} (hτ : 0 < τ) {n W : ℕ} (hn : 4 ≤ n) (hW : 0 < W)
    (i : Fin (n - 3)) :
    |rvCosineTest τ m (((n - 3 - i.val : ℕ) : ℝ) / W) -
        Real.cos (2 * Real.pi * m * ((i.val + 2 : ℕ) : ℝ) / n)| ≤
      2 * Real.pi * |(m : ℝ)| * (((n - 3 : ℕ) : ℝ) * |1 / (τ * W) - 1 / n| + 1 / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hi := i.isLt
  have hR : (((n - 3 : ℕ) : ℝ)) = (n : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hRi : (((n - 3 - i.val : ℕ) : ℝ)) = (n : ℝ) - 3 - i.val := by
    rw [Nat.cast_sub (by omega), hR]
  have hI2 : (((i.val + 2 : ℕ) : ℝ)) = (i.val : ℝ) + 2 := by push_cast; ring
  have hcos : Real.cos (2 * Real.pi * m * ((i.val + 2 : ℕ) : ℝ) / n) =
      Real.cos (2 * Real.pi * m * ((n : ℝ) - 2 - i.val) / n) := by
    rw [← Real.cos_int_mul_two_pi_sub _ m]
    congr 1
    rw [hI2]; field_simp; ring
  rw [hcos, rvCosineTest, hRi]
  refine (Real.abs_cos_sub_cos_le _ _).trans ?_
  have hii : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hiR : (i.val : ℝ) ≤ (n : ℝ) - 3 := by
    have : (i.val : ℝ) < ((n - 3 : ℕ) : ℝ) := by exact_mod_cast hi
    rw [hR] at this; linarith
  have key : 2 * Real.pi * m * (((n : ℝ) - 3 - i.val) / W) / τ -
      2 * Real.pi * m * ((n : ℝ) - 2 - i.val) / n =
      2 * Real.pi * m * ((((n : ℝ) - 3 - i.val)) * (1 / (τ * W) - 1 / n) - 1 / n) := by
    field_simp; ring
  rw [key, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, hR]
  have h2 : |(2 : ℝ)| = 2 := abs_two
  rw [h2]
  have hπ : 0 ≤ 2 * Real.pi * |(m : ℝ)| := by positivity
  have hin : |((n : ℝ) - 3 - i.val) * (1 / (τ * W) - 1 / n) - 1 / n| ≤
      ((n : ℝ) - 3) * |1 / (τ * W) - 1 / n| + 1 / n := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 3 - i.val),
      abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
    have := abs_nonneg (1 / (τ * W) - 1 / n)
    nlinarith
  calc 2 * Real.pi * |(m : ℝ)| * |((n : ℝ) - 3 - i.val) * (1 / (τ * W) - 1 / n) - 1 / n|
      ≤ 2 * Real.pi * |(m : ℝ)| * (((n : ℝ) - 3) * |1 / (τ * W) - 1 / n| + 1 / n) :=
        mul_le_mul_of_nonneg_left hin hπ

/-- The source-weighted ratio against the cosine coefficient of the lead profile:
`rvRatio² ≤ 3 c₀² + 3 ε² + 3 a_port`. -/
theorem rv_ratio_sq_le (m : ℤ) (τ : ℝ) (b e : ℝ) {n W : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ i : Fin (n - 3), |rvCosineTest τ m (((n - 3 - i.val : ℕ) : ℝ) / W) -
        Real.cos (2 * Real.pi * m * ((i.val + 2 : ℕ) : ℝ) / n)| ≤ ε)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    rvRatio (rvCosineTest τ m) b e W (n - 3) x ^ 2 ≤
      3 * rvLeadCos m b e n W x ^ 2 + 3 * ε ^ 2 + 3 * portFraction b e W (n - 3) x := by
  set tot := totalLeadMass b e W (n - 3) x
  have htot : 0 ≤ tot := rv_totalLeadMass_nonneg b e W (n - 3) x
  set ρ : Fin (n - 3) ⊕ Fin 2 → ℝ := fun y => leadPositionMass b e W (n - 3) x.1 x.2 y / tot
  have hρ : ∀ y, 0 ≤ ρ y := fun y => div_nonneg (leadPositionMass_nonneg _ _ _ _ _) htot
  have hsum : ∑ i : Fin (n - 3), ρ (Sum.inl i) + ∑ j : Fin 2, ρ (Sum.inr j) ≤ 1 := by
    simp only [ρ, ← Finset.sum_div]
    rw [← add_div]
    have : ∑ i : Fin (n - 3), leadPositionMass b e W (n - 3) x.1 x.2 (Sum.inl i) +
        ∑ j : Fin 2, leadPositionMass b e W (n - 3) x.1 x.2 (Sum.inr j) = tot := by
      simp only [tot, totalLeadMass, Fintype.sum_sum_type]
    rw [this]
    rcases htot.lt_or_eq with hlt | heq
    · rw [div_self hlt.ne']
    · rw [← heq, div_zero]; exact zero_le_one
  have hZ : rvRatio (rvCosineTest τ m) b e W (n - 3) x =
      ∑ i : Fin (n - 3), rvCosineTest τ m (((n - 3 - i.val : ℕ) : ℝ) / W) * ρ (Sum.inl i) := by
    rw [rvRatio, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ρ]; ring
  have hc : rvLeadCos m b e n W x =
      ∑ i : Fin (n - 3), ρ (Sum.inl i) * Real.cos (2 * Real.pi * m * ((i.val + 2 : ℕ) : ℝ) / n) +
        ∑ j : Fin 2, ρ (Sum.inr j) *
          Real.cos (2 * Real.pi * m * (leadRingBlock (n - 3) (Sum.inr j) : ℕ) / n) := by
    rw [rvLeadCos, Fintype.sum_sum_type]
    rfl
  have hπ : portFraction b e W (n - 3) x = ∑ j : Fin 2, ρ (Sum.inr j) := by
    rw [portFraction, portLeadMass, Finset.sum_div]
  have hπ0 : 0 ≤ portFraction b e W (n - 3) x := portFraction_nonneg _ _ _ _ _
  have hπ1 : portFraction b e W (n - 3) x ≤ 1 := portFraction_le_one _ _ _ _ _
  -- `|Z - c₀| ≤ ε + a_port`
  have hdiff : |rvRatio (rvCosineTest τ m) b e W (n - 3) x - rvLeadCos m b e n W x| ≤
      ε + portFraction b e W (n - 3) x := by
    rw [hZ, hc, hπ]
    have e1 : ∑ i : Fin (n - 3), rvCosineTest τ m (((n - 3 - i.val : ℕ) : ℝ) / W) * ρ (Sum.inl i) -
        (∑ i : Fin (n - 3), ρ (Sum.inl i) *
            Real.cos (2 * Real.pi * m * ((i.val + 2 : ℕ) : ℝ) / n) +
          ∑ j : Fin 2, ρ (Sum.inr j) *
            Real.cos (2 * Real.pi * m * (leadRingBlock (n - 3) (Sum.inr j) : ℕ) / n)) =
        ∑ i : Fin (n - 3), ρ (Sum.inl i) * (rvCosineTest τ m (((n - 3 - i.val : ℕ) : ℝ) / W) -
            Real.cos (2 * Real.pi * m * ((i.val + 2 : ℕ) : ℝ) / n)) -
          ∑ j : Fin 2, ρ (Sum.inr j) *
            Real.cos (2 * Real.pi * m * (leadRingBlock (n - 3) (Sum.inr j) : ℕ) / n) := by
      rw [sub_add_eq_sub_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e1]
    have h1 : |∑ i : Fin (n - 3), ρ (Sum.inl i) * (rvCosineTest τ m (((n - 3 - i.val : ℕ) : ℝ) / W) -
        Real.cos (2 * Real.pi * m * ((i.val + 2 : ℕ) : ℝ) / n))| ≤
        ε * ∑ i : Fin (n - 3), ρ (Sum.inl i) := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_of_nonneg (hρ _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hε i) (hρ _)
    have h2 : |∑ j : Fin 2, ρ (Sum.inr j) *
        Real.cos (2 * Real.pi * m * (leadRingBlock (n - 3) (Sum.inr j) : ℕ) / n)| ≤
        ∑ j : Fin 2, ρ (Sum.inr j) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_of_nonneg (hρ _)]
      exact mul_le_of_le_one_right (hρ _) (Real.abs_cos_le_one _)
    have hsI : ∑ i : Fin (n - 3), ρ (Sum.inl i) ≤ 1 := by
      have : 0 ≤ ∑ j : Fin 2, ρ (Sum.inr j) := Finset.sum_nonneg fun j _ => hρ _
      linarith
    have h3 : ε * ∑ i : Fin (n - 3), ρ (Sum.inl i) ≤ ε := mul_le_of_le_one_right hε0 hsI
    refine (abs_sub _ _).trans ?_
    linarith
  set Z := rvRatio (rvCosineTest τ m) b e W (n - 3) x
  set c₀ := rvLeadCos m b e n W x
  set π₀ := portFraction b e W (n - 3) x
  have hZb : |Z| ≤ |c₀| + ε + π₀ := by
    have := abs_sub_abs_le_abs_sub Z c₀
    linarith
  have hZ2 : Z ^ 2 ≤ (|c₀| + ε + π₀) ^ 2 := by
    rw [← sq_abs Z]
    exact pow_le_pow_left₀ (abs_nonneg _) hZb 2
  have hc2 : |c₀| ^ 2 = c₀ ^ 2 := sq_abs _
  nlinarith [sq_nonneg (|c₀| - ε), sq_nonneg (|c₀| - π₀), sq_nonneg (ε - π₀), abs_nonneg c₀]

end BlockBand.Endpoints
