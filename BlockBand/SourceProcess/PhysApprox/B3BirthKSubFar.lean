module

public import BlockBand.SourceProcess.PhysApprox.B3BirthKClose
public import BlockBand.SourceProcess.PhysApprox.B3BirthFresh
public import BlockBand.SourceProcess.PhysApprox.ConjSym

/-!
# The far birth masses `BirthKFarIn`, `BirthKFarOut`

Measure `probedPathLaw W np b` (path and independent probes `g_c ~ CN(0, I_W)`); domain
`ComplexSourceLawDomain`, `0 < s < τ`, `0 < h < 1`; the probe `i` born at `j = ⌊Wτ_i⌋ ∈ [⌊Ws⌋, ⌊WT⌋)`, read at
its birth length `j + 1`. `F = 1 − P` is the far port.

* `lintegral_l2_sq_mul_probeFrame` (Gaussian average over the probe, every `ω`):
  `E‖(MV_n)_i‖² = (m_i/W) E Re Tr(MᴴM Y_{n;k})`, `k = ⌊Wτ_i⌋ < n`, for every measurable `M`.
* `lintegral_far_out_eq_in`: `E Re Tr(F𝕊Y𝕊ᴴ) = E Re Tr(FY)` (conjugation symmetry,
  `Y(ω̄) = conj(𝕊Y𝕊ᴴ)`, `growthPathLaw` conjugation invariant).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.BirthKSub

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingLeak BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## Contractions
-/

section Contraction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem dot_mulVec_self {ρ : Type*} [Fintype ρ] (X : Matrix ρ ι ℂ) (w : ι → ℂ) :
    star (X *ᵥ w) ⬝ᵥ (X *ᵥ w) = star w ⬝ᵥ ((Xᴴ * X) *ᵥ w) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

omit [DecidableEq ι] in
theorem re_dot_self_nonneg (w : ι → ℂ) : 0 ≤ (star w ⬝ᵥ w).re := by
  rw [dot_self_eq, Complex.ofReal_re]
  exact Finset.sum_nonneg fun x _ => sq_nonneg _

/-- An orthogonal projection is a contraction: `‖Qw‖² ≤ ‖w‖²`. -/
theorem re_dot_proj_le {Q : Matrix ι ι ℂ} (hQH : Qᴴ = Q) (hQQ : Q * Q = Q) (w : ι → ℂ) :
    (star (Q *ᵥ w) ⬝ᵥ (Q *ᵥ w)).re ≤ (star w ⬝ᵥ w).re := by
  have hC : (1 - Q)ᴴ * (1 - Q) = 1 - Q := by
    rw [conjTranspose_sub, conjTranspose_one, hQH, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hQQ, sub_self, sub_zero]
  have e : star w ⬝ᵥ w = star (Q *ᵥ w) ⬝ᵥ (Q *ᵥ w) + star ((1 - Q) *ᵥ w) ⬝ᵥ ((1 - Q) *ᵥ w) := by
    rw [dot_mulVec_self, dot_mulVec_self, hC, hQH, hQQ, ← dotProduct_add, ← add_mulVec,
      add_sub_cancel, one_mulVec]
  rw [e, Complex.add_re]
  linarith [re_dot_self_nonneg ((1 - Q) *ᵥ w)]

/-- **`‖Xv‖ ≤ ‖Fv‖`** when `XᴴX` is idempotent and `XF = X`. -/
theorem re_dot_mulVec_le {X F : Matrix ι ι ℂ} (hXX : (Xᴴ * X) * (Xᴴ * X) = Xᴴ * X)
    (hXF : X * F = X) (v : ι → ℂ) :
    (star (X *ᵥ v) ⬝ᵥ (X *ᵥ v)).re ≤ (star (F *ᵥ v) ⬝ᵥ (F *ᵥ v)).re := by
  set Q := Xᴴ * X
  have hQH : Qᴴ = Q := by simp only [Q, conjTranspose_mul, conjTranspose_conjTranspose]
  have e1 : X *ᵥ v = X *ᵥ (F *ᵥ v) := by rw [mulVec_mulVec, hXF]
  have e2 : star (X *ᵥ (F *ᵥ v)) ⬝ᵥ (X *ᵥ (F *ᵥ v)) =
      star (Q *ᵥ (F *ᵥ v)) ⬝ᵥ (Q *ᵥ (F *ᵥ v)) := by
    rw [dot_mulVec_self, dot_mulVec_self, hQH, hXX]
  rw [e1, e2]
  exact re_dot_proj_le hQH hXX _

end Contraction

/-- The column `i` of a product: `(AB)ᵀ_i = A (Bᵀ_i)`. -/
theorem col_mul {ρ κ c : Type*} [Fintype κ] (A : Matrix ρ κ ℂ) (B : Matrix κ c ℂ) (i : c) :
    (A * B)ᵀ i = A *ᵥ (Bᵀ i) := by
  funext z
  simp [Matrix.mul_apply, mulVec, dotProduct]

variable {W np : ℕ}

theorem one_sub_nearProjection_conjTranspose : (1 - nearProjection W)ᴴ = 1 - nearProjection W := by
  rw [conjTranspose_sub, conjTranspose_one,
    BlockBand.Transmission.Bridge.nearProjection_conjTranspose]

theorem one_sub_nearProjection_mul_self :
    (1 - nearProjection W) * (1 - nearProjection W) = 1 - nearProjection W := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, BlockBand.Transmission.Bridge.nearProjection_mul_self, sub_self, sub_zero]

theorem farEmbed_mul_one_sub_nearProjection (X : Matrix (Fin W) (Fin W) ℂ) :
    farEmbed X * (1 - nearProjection W) = farEmbed X := by
  rw [Matrix.mul_sub, Matrix.mul_one]
  have : farEmbed X * nearProjection W = 0 := farEmbed_mul_nearPortProj X
  rw [this, sub_zero]

/-!
## The two far amplitudes are dominated by the far port
-/

/-- **`‖(AV)_i‖ ≤ ‖((1 − P)V)_i‖`** (`farEmbed A_-` is a Hermitian idempotent). -/
theorem l2_birthKIn_le (b E s h : ℝ) (τ m : Fin np → ℝ) (n : ℕ) (x : ProbedPath W np)
    (i : Fin np) :
    l2 ((birthKIn b E s h τ m W n x)ᵀ i) ≤
      l2 (((1 - nearProjection W) * probeFrame b E W n τ m x)ᵀ i) := by
  refine l2_le_of_sq_le ?_
  rw [birthKIn, col_mul, col_mul]
  set A := farEmbed (omittedProj b E h W (closeLen s W) x.1)
  have hAH : Aᴴ = A := omittedEmbed_conjTranspose b E h _ _
  have hAA : A * A = A := omittedEmbed_mul_self b E h _ _
  exact re_dot_mulVec_le (by rw [hAH, hAA, hAA]) (farEmbed_mul_one_sub_nearProjection _) _

/-- **`‖(Π𝕊V)_i‖ ≤ ‖((1 − P)𝕊V)_i‖`** for `h² < 1` (`ΠΠᴴ = A_-`, `A_-Π = Π`). -/
theorem l2_birthKOut_le (b E s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (n : ℕ)
    (x : ProbedPath W np) (i : Fin np) :
    l2 ((birthKOut b E s h τ m W n x)ᵀ i) ≤
      l2 (((1 - nearProjection W) * scatteringMatrix b E W n x.1 *
        probeFrame b E W n τ m x)ᵀ i) := by
  refine l2_le_of_sq_le ?_
  rw [birthKOut, Matrix.mul_assoc, Matrix.mul_assoc, col_mul, col_mul]
  set Pi := closingPairing b E h W (closeLen s W) x.1
  have hPP : Pi * Piᴴ = omittedProj b E h W (closeLen s W) x.1 :=
    closingPairing_mul_conj b E h hh _ _
  have hAP : omittedProj b E h W (closeLen s W) x.1 * Pi = Pi :=
    omittedProj_mul_closingPairing b E h _ _
  have hXX : (farEmbed Pi)ᴴ * farEmbed Pi * ((farEmbed Pi)ᴴ * farEmbed Pi) =
      (farEmbed Pi)ᴴ * farEmbed Pi := by
    rw [farEmbed_conjTranspose, farEmbed_mul, farEmbed_mul]
    congr 1
    rw [show Piᴴ * Pi * (Piᴴ * Pi) = Piᴴ * (Pi * Piᴴ * Pi) by simp only [Matrix.mul_assoc],
      hPP, hAP]
  exact re_dot_mulVec_le hXX (farEmbed_mul_one_sub_nearProjection _) _

/-!
## The Gaussian average over the newborn probe
-/

/-- The block column `M𝒰ᴴι_p` seen by the probe of the block at position `p`. -/
def colMap (b E : ℝ) (W n : ℕ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (p : Fin n)
    (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  (M * (boundaryToInterior b E W n ω)ᴴ).submatrix id fun a => (p, a)

/-- The column of `MV_n` of a probe on the path: `(MV)_i = √(m_i/W) (M𝒰ᴴι_p) g_i`. -/
theorem col_mul_probeFrame (b E : ℝ) (τ m : Fin np → ℝ) (i : Fin np) {n : ℕ}
    (hi : ⌊(W : ℝ) * τ i⌋₊ < n) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (x : ProbedPath W np) :
    (M * probeFrame b E W n τ m x)ᵀ i = ((Real.sqrt (m i / W) : ℝ) : ℂ) •
      (colMap b E W n M ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ x.1 *ᵥ x.2 i) := by
  have hJ := congrFun (probeColumn_eq_tagVector n τ m x.2 i hi)
  funext z
  rw [probeFrame, ← Matrix.mul_assoc, transpose_apply, Matrix.mul_apply]
  simp only [hJ, tagVector, Fintype.sum_prod_type, colMap, mulVec, dotProduct, submatrix_apply,
    id, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_eq_single (⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ : Fin n)]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp only [↓reduceIte]
    ring
  · intro q _ hq
    simp [hq]
  · simp

/-- `‖Lg‖² = Q_{LᴴL}(g)`. -/
theorem dot_mulVec_eq_quad {κ : Type*} [Fintype κ] (L : Matrix (Fin 2 × Fin W) κ ℂ)
    (g : κ → ℂ) :
    star (L *ᵥ g) ⬝ᵥ (L *ᵥ g) = Counting.complexQuadraticForm (Lᴴ * L) g := by
  rw [dot_mulVec_self]
  simp only [Counting.complexQuadraticForm, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  simp only [Complex.star_def]
  ring

/-- `Tr(LᴴL) = Tr(MᴴM Y_{n;k})` for `L = M𝒰ᴴι_p`, `p = n − 1 − k`. -/
theorem trace_colMap (b E : ℝ) {n k : ℕ} (hk : k < n)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : GrowthPath W) :
    ((colMap b E W n M ⟨n - 1 - k, by omega⟩ ω)ᴴ * colMap b E W n M ⟨n - 1 - k, by omega⟩ ω).trace =
      (Mᴴ * M * tagResponse b E W n k ω).trace := by
  set U := boundaryToInterior b E W n ω
  set p : Fin n := ⟨n - 1 - k, by omega⟩
  have e1 : (colMap b E W n M p ω)ᴴ * colMap b E W n M p ω =
      ((M * Uᴴ)ᴴ * (M * Uᴴ)).submatrix (fun a => (p, a)) fun a => (p, a) := by
    rw [colMap, conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id]
  have e2 : (Mᴴ * M * tagResponse b E W n k ω).trace =
      ((M * Uᴴ)ᴴ * (M * Uᴴ) * tagProjection W n k).trace := by
    rw [tagResponse, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [show Mᴴ * M * (Uᴴ * tagProjection W n k * U) = (Mᴴ * M * Uᴴ * tagProjection W n k) * U by
      simp only [Matrix.mul_assoc], trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e1, e2, tagProjection]
  simp only [trace, diag, submatrix_apply, mul_diagonal]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single p]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [p, hk]
  · intro q _ hq
    refine Finset.sum_eq_zero fun a _ => ?_
    have : ¬ (k < n ∧ q.val = n - 1 - k) := fun h => hq (Fin.ext h.2)
    simp [this]
  · simp

theorem measurable_boundaryToInterior' (b E : ℝ) (n : ℕ) :
    Measurable (boundaryToInterior b E W n) :=
  Measurable.of_eval_matrix _ fun _ _ => (measurable_fullInverse b E n).eval_matrix

theorem l2_ofReal_smul {κ : Type*} [Fintype κ] (r : ℝ) (w : κ → ℂ) :
    l2 ((r : ℂ) • w) = |r| * l2 w := by
  rw [l2, l2, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- `‖(MV_n)_i‖ = √(m_i/W) ‖(M𝒰ᴴι_p) g_i‖`. -/
theorem l2_col_mul_probeFrame (b E : ℝ) (τ m : Fin np → ℝ) (i : Fin np) {n : ℕ}
    (hi : ⌊(W : ℝ) * τ i⌋₊ < n) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (x : ProbedPath W np) :
    l2 ((M * probeFrame b E W n τ m x)ᵀ i) = Real.sqrt (m i / W) *
      l2 (colMap b E W n M ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ x.1 *ᵥ x.2 i) := by
  rw [col_mul_probeFrame b E τ m i hi, l2_ofReal_smul, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem measurable_l2_mulVec {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    {L : α → Matrix (Fin 2 × Fin W) κ ℂ} (hL : Measurable L) :
    Measurable fun z : α × (κ → ℂ) => l2 (L z.1 *ᵥ z.2) := by
  refine continuous_l2.measurable.comp (measurable_pi_iff.2 fun y => ?_)
  simp only [mulVec, dotProduct]
  exact Finset.measurable_sum _ fun a _ =>
    ((hL.eval_matrix).comp measurable_fst).mul ((measurable_pi_apply a).comp measurable_snd)

/-- **The Gaussian average of a squared norm**: `E‖Lg‖² = Re Tr(LᴴL)`, `g ~ CN(0, I_W)`. -/
theorem lintegral_l2_sq_mulVec (L : Matrix (Fin 2 × Fin W) (Fin W) ℂ) :
    ∫⁻ v, ENNReal.ofReal (l2 (L *ᵥ v) ^ 2) ∂circularVectorLaw (Fin W) =
      ENNReal.ofReal (Lᴴ * L).trace.re := by
  have hpt : ∀ v, l2 (L *ᵥ v) ^ 2 = (Counting.complexQuadraticForm (Lᴴ * L) v).re := by
    intro v
    rw [l2_sq, dot_mulVec_eq_quad]
  simp_rw [hpt]
  have h0 : 0 ≤ᵐ[circularVectorLaw (Fin W)] fun v =>
      (Counting.complexQuadraticForm (Lᴴ * L) v).re :=
    ae_of_all _ fun v => by
      simp only [Pi.zero_apply]
      rw [← hpt]
      positivity
  have hI : Integrable (fun v => (Counting.complexQuadraticForm (Lᴴ * L) v).re)
      (circularVectorLaw (Fin W)) := (Birth.integrable_quad' (Lᴴ * L)).re
  have hre := integral_re (Birth.integrable_quad' (Lᴴ * L))
  simp only [RCLike.re_to_complex] at hre
  rw [← ofReal_integral_eq_lintegral_ofReal hI h0, hre, Birth.integral_quad']

theorem measurable_colMap (b E : ℝ) {n : ℕ} (p : Fin n) {α : Type*} [MeasurableSpace α]
    {M : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ω : α → GrowthPath W}
    (hM : Measurable M) (hω : Measurable ω) :
    Measurable fun a => colMap b E W n (M a) p (ω a) :=
  Measurable.of_eval_matrix _ fun z a => by
    simp only [colMap, submatrix_apply, id]
    exact (measurable_matrix_mul' hM (measurable_matrix_conjTranspose'
      ((measurable_boundaryToInterior' b E n).comp hω))).eval_matrix

/-- **The Gaussian average over the probe**:
`E‖(MV_n)_i‖² = (m_i/W) E Re Tr(MᴴM Y_{n;k})`, `k = ⌊Wτ_i⌋ < n`. -/
theorem lintegral_l2_sq_mul_probeFrame (b E : ℝ) (τ m : Fin np → ℝ) (i : Fin np)
    (hm : 0 ≤ m i) {n : ℕ} (hi : ⌊(W : ℝ) * τ i⌋₊ < n)
    {M : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hM : Measurable M) :
    ∫⁻ x, ENNReal.ofReal (l2 ((M x.1 * probeFrame b E W n τ m x)ᵀ i) ^ 2)
        ∂probedPathLaw W np b =
      ∫⁻ ω, ENNReal.ofReal (m i / W * ((M ω)ᴴ * M ω *
        tagResponse b E W n ⌊(W : ℝ) * τ i⌋₊ ω).trace.re) ∂growthPathLaw W b := by
  set p : Fin n := ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩
  set c : ℝ := m i / W
  have hc : 0 ≤ c := div_nonneg hm (Nat.cast_nonneg W)
  set F : GrowthPath W × (Fin W → ℂ) → ℝ≥0∞ := fun z => ENNReal.ofReal c *
    ENNReal.ofReal (l2 (colMap b E W n (M z.1) p z.1 *ᵥ z.2) ^ 2) with hFdef
  have hpt : ∀ x : ProbedPath W np,
      ENNReal.ofReal (l2 ((M x.1 * probeFrame b E W n τ m x)ᵀ i) ^ 2) = F (x.1, x.2 i) := by
    intro x
    rw [l2_col_mul_probeFrame b E τ m i hi, mul_pow, Real.sq_sqrt hc, ENNReal.ofReal_mul hc]
  have hmL : Measurable fun ω => colMap b E W n (M ω) p ω :=
    measurable_colMap b E p hM measurable_id
  have hF : Measurable F :=
    measurable_const.mul (((measurable_l2_mulVec hmL).pow_const 2).ennreal_ofReal)
  simp_rw [hpt]
  rw [probedPathLaw, lintegral_prod (fun x : ProbedPath W np => F (x.1, x.2 i))
    (hF.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).aemeasurable]
  refine lintegral_congr fun ω => ?_
  have hg : Measurable fun g : Fin W → ℂ => F (ω, g) := hF.comp measurable_prodMk_left
  have e := (measurePreserving_eval (fun _ : Fin np => circularVectorLaw (Fin W)) i).lintegral_comp
    hg
  refine e.trans ?_
  simp only [hFdef]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_l2_sq_mulVec,
    trace_colMap b E hi, ← ENNReal.ofReal_mul hc]

/-!
## The far output mass equals the far input mass in law
-/

theorem matConj_nearProjection : matConj (nearProjection W) = nearProjection W := by
  ext x y
  simp only [matConj_apply, nearProjection, diagonal_apply]
  split_ifs <;> simp

theorem matConj_one_sub_nearProjection : matConj (1 - nearProjection W) = 1 - nearProjection W := by
  rw [matConj_sub, matConj_one, matConj_nearProjection]

/-- **`E Re Tr(F𝕊Y𝕊ᴴ) = E Re Tr(FY)`** (conjugation symmetry of the path law). -/
theorem lintegral_far_out_eq_in (b E : ℝ) (c : ℝ) (n k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (c * (((1 - nearProjection W) * scatteringMatrix b E W n ω)ᴴ *
        ((1 - nearProjection W) * scatteringMatrix b E W n ω) * tagResponse b E W n k ω).trace.re)
      ∂growthPathLaw W b =
    ∫⁻ ω, ENNReal.ofReal (c * ((1 - nearProjection W) * tagResponse b E W n k ω).trace.re)
      ∂growthPathLaw W b := by
  rw [← lintegral_conjPath b (fun ω => ENNReal.ofReal (c * ((1 - nearProjection W) *
    tagResponse b E W n k ω).trace.re))]
  refine lintegral_congr_ae ?_
  filter_upwards [BlockBand.Transmission.Bridge.ae_growth_isHermitian W b] with ω hA
  congr 2
  set S := scatteringMatrix b E W n ω
  set Y := tagResponse b E W n k ω
  rw [tagResponse_conjPath b E n k ω hA, ← matConj_one_sub_nearProjection, ← matConj_mul,
    re_trace_matConj, matConj_one_sub_nearProjection, conjTranspose_mul,
    one_sub_nearProjection_conjTranspose]
  rw [show Sᴴ * (1 - nearProjection W) * ((1 - nearProjection W) * S) * Y =
      Sᴴ * ((1 - nearProjection W) * (1 - nearProjection W) * (S * Y)) by
    simp only [Matrix.mul_assoc], one_sub_nearProjection_mul_self, trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rfl

/-!
## The far birth masses from the newborn far mass
-/

/-- **Newborn far mass** (a path-only statement): the far
birth mass of a newborn tag, `E[W⁻¹ Re Tr((1 − P)Y_{j+1;j})] → 0`, uniformly over the birth
lengths `⌊Ws⌋ ≤ j < ⌊WT⌋`. -/
def NewbornFarMass : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s →
    ∀ θ : ℝ, 0 < θ → ∀ᶠ W : ℕ in atTop, ∀ j : ℕ, ⌊(W : ℝ) * s⌋₊ ≤ j →
      j < ⌊(W : ℝ) * T⌋₊ →
      ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ *
          ((1 - nearProjection W) * tagResponse b E W (j + 1) j ω).trace.re)
        ∂growthPathLaw W b ≤ ENNReal.ofReal θ

/-- `ofReal (m/W · x) = ofReal m · ofReal (W⁻¹ x)` for `m ≥ 0`. -/
theorem ofReal_div_mul (W : ℕ) {m : ℝ} (hm : 0 ≤ m) (x : ℝ) :
    ENNReal.ofReal (m / W * x) = ENNReal.ofReal m * ENNReal.ofReal ((W : ℝ)⁻¹ * x) := by
  rw [← ENNReal.ofReal_mul hm, div_eq_mul_inv, mul_assoc]

/-- The final arithmetic: `ofReal m · ofReal (δ/(m+1)) ≤ ofReal δ`. -/
theorem ofReal_mul_le_of_le {m δ : ℝ} (hm : 0 ≤ m) (hδ : 0 < δ) {X : ℝ≥0∞}
    (hX : X ≤ ENNReal.ofReal (δ / (m + 1))) : ENNReal.ofReal m * X ≤ ENNReal.ofReal δ := by
  calc ENNReal.ofReal m * X ≤ ENNReal.ofReal m * ENNReal.ofReal (δ / (m + 1)) := by gcongr
    _ = ENNReal.ofReal (m * (δ / (m + 1))) := (ENNReal.ofReal_mul hm).symm
    _ ≤ ENNReal.ofReal δ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith

/-- **`BirthKFarIn`** from the newborn far mass (no use of `h`). -/
theorem birthKFarIn_of_mass (hN : NewbornFarMass) : BirthKFarIn := by
  intro b E np τ m T s h hD hs _ _ _ δ hδ i
  obtain ⟨hb0, hb, hE1, hE2, -, -, hm, -⟩ := hD
  have hδ' : 0 < δ / (m i + 1) := div_pos hδ (by linarith [hm i])
  filter_upwards [hN b hb0 hb E hE1 hE2 s T hs _ hδ'] with W hW
  intro j hj1 hj2 hji
  have hi : ⌊(W : ℝ) * τ i⌋₊ < j + 1 := by omega
  calc ∫⁻ x, ENNReal.ofReal (l2 ((birthKIn b E s h τ m W (j + 1) x)ᵀ i) ^ 2)
        ∂probedPathLaw W np b
      ≤ ∫⁻ x, ENNReal.ofReal (l2 (((1 - nearProjection W) *
          probeFrame b E W (j + 1) τ m x)ᵀ i) ^ 2) ∂probedPathLaw W np b :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (l2_nonneg _)
          (l2_birthKIn_le b E s h τ m (j + 1) x i) 2)
    _ = ∫⁻ ω, ENNReal.ofReal (m i / W * ((1 - nearProjection W) *
          tagResponse b E W (j + 1) j ω).trace.re) ∂growthPathLaw W b := by
        rw [lintegral_l2_sq_mul_probeFrame b E τ m i (hm i) hi
          (M := fun _ => 1 - nearProjection W) measurable_const]
        simp only [one_sub_nearProjection_conjTranspose, one_sub_nearProjection_mul_self, hji]
    _ = ENNReal.ofReal (m i) * ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ * ((1 - nearProjection W) *
          tagResponse b E W (j + 1) j ω).trace.re) ∂growthPathLaw W b := by
        simp_rw [ofReal_div_mul W (hm i)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal δ := ofReal_mul_le_of_le (hm i) hδ (hW j hj1 hj2)

/-- **`BirthKFarOut`** from the newborn far mass (`h < 1`; conjugation symmetry). -/
theorem birthKFarOut_of_mass (hN : NewbornFarMass) : BirthKFarOut := by
  intro b E np τ m T s h hD hs _ hh0 hh1 δ hδ i
  obtain ⟨hb0, hb, hE1, hE2, -, -, hm, -⟩ := hD
  have hh : h ^ 2 < 1 := by nlinarith
  have hδ' : 0 < δ / (m i + 1) := div_pos hδ (by linarith [hm i])
  filter_upwards [hN b hb0 hb E hE1 hE2 s T hs _ hδ'] with W hW
  intro j hj1 hj2 hji
  have hi : ⌊(W : ℝ) * τ i⌋₊ < j + 1 := by omega
  calc ∫⁻ x, ENNReal.ofReal (l2 ((birthKOut b E s h τ m W (j + 1) x)ᵀ i) ^ 2)
        ∂probedPathLaw W np b
      ≤ ∫⁻ x, ENNReal.ofReal (l2 (((1 - nearProjection W) * scatteringMatrix b E W (j + 1) x.1 *
          probeFrame b E W (j + 1) τ m x)ᵀ i) ^ 2) ∂probedPathLaw W np b :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (l2_nonneg _)
          (l2_birthKOut_le b E s h hh τ m (j + 1) x i) 2)
    _ = ∫⁻ ω, ENNReal.ofReal (m i / W * ((1 - nearProjection W) *
          tagResponse b E W (j + 1) j ω).trace.re) ∂growthPathLaw W b := by
        rw [lintegral_l2_sq_mul_probeFrame b E τ m i (hm i) hi
          (M := fun ω => (1 - nearProjection W) * scatteringMatrix b E W (j + 1) ω)
          (measurable_matrix_mul' measurable_const (measurable_scatteringMatrix b E (j + 1))),
          hji, lintegral_far_out_eq_in]
    _ = ENNReal.ofReal (m i) * ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ * ((1 - nearProjection W) *
          tagResponse b E W (j + 1) j ω).trace.re) ∂growthPathLaw W b := by
        simp_rw [ofReal_div_mul W (hm i)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal δ := ofReal_mul_le_of_le (hm i) hδ (hW j hj1 hj2)

end BlockBand.SourceProcess.PhysApprox.B3.BirthKSub
