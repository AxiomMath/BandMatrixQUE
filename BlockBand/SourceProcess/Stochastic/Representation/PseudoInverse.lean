module
public import BlockBand.SourceProcess.Stochastic.Levy.Penrose
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Field.Basic
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# A Borel Moore–Penrose pseudoinverse

For `A ∈ ℝ^{d×m}`, the Tikhonov regularizations `P_ε = (AᵀA + ε I)⁻¹ Aᵀ` (`ε > 0`) converge as
`ε ↓ 0` (along `ε_n = 1/(n+1)`) to `pinv A`, which satisfies the four Penrose identities.

* `exists_sq_factor`: `Aᵀ = (AᵀA)(AᵀA) Q` for some `Q` (`ran Aᵀ = ran AᵀA`, rank argument).
* `abs_smul_inv_gramReg_le`: `|ε (AᵀA + εI)⁻¹_{ij}| ≤ 1`.
* `tikhonov_eq`: `P_ε = SQ - εQ + ε (εR_ε) Q` with `S = AᵀA`, `R_ε = (S + εI)⁻¹`; hence
  **`tendsto_tikhonov`**: `P_{ε_n} → pinv A`.
* **`isMoorePenrose_pinv`**: `IsMoorePenrose A (pinv A)` (the Penrose identities), by passing
  to the limit in `A P_ε A = A - ε P_εᵀ`,
  `(A P_ε)ᵀ = A P_ε`, `(P_ε A)ᵀ = P_ε A` and `P_ε A P = P_ε`.
* **`measurable_pinv_comp`**: for `σ : X → ℝ^{d×m}` with measurable entries, every entry of
  `x ↦ pinv (σ x)` is measurable (pointwise limit of continuous functions of `σ x`).
-/

namespace BlockBand.SourceProcess.Stochastic.Representation
open Matrix Filter Topology MeasureTheory
open BlockBand.SourceProcess.Stochastic.Levy

variable {d m : ℕ}

/-- `(AᵀA + εI)`. -/
def gramReg (A : Matrix (Fin d) (Fin m) ℝ) (ε : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Aᵀ * A + ε • (1 : Matrix (Fin m) (Fin m) ℝ)

/-- The Tikhonov regularization `P_ε = (AᵀA + εI)⁻¹ Aᵀ`. -/
def tikhonov (A : Matrix (Fin d) (Fin m) ℝ) (ε : ℝ) : Matrix (Fin m) (Fin d) ℝ :=
  (gramReg A ε)⁻¹ * Aᵀ

/-- The regularization sequence `ε_n = 1/(n+1)`. -/
def regSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem regSeq_pos (n : ℕ) : 0 < regSeq n := by unfold regSeq; positivity

theorem tendsto_regSeq : Tendsto regSeq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- **The Moore–Penrose pseudoinverse** as the limit of Tikhonov regularizations. -/
def pinv (A : Matrix (Fin d) (Fin m) ℝ) : Matrix (Fin m) (Fin d) ℝ :=
  limUnder atTop fun n => tikhonov A (regSeq n)

theorem dotProduct_gramReg (A : Matrix (Fin d) (Fin m) ℝ) (ε : ℝ) (u : Fin m → ℝ) :
    u ⬝ᵥ (gramReg A ε *ᵥ u) = (A *ᵥ u) ⬝ᵥ (A *ᵥ u) + ε * (u ⬝ᵥ u) := by
  rw [gramReg, add_mulVec, dotProduct_add, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

theorem dotProduct_self_nonneg' {n : ℕ} (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem isUnit_det_gramReg (A : Matrix (Fin d) (Fin m) ℝ) {ε : ℝ} (hε : 0 < ε) :
    IsUnit (gramReg A ε).det := by
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  obtain ⟨u, hu, hzero⟩ := (exists_mulVec_eq_zero_iff (M := gramReg A ε)).2 h0
  have h := dotProduct_gramReg A ε u
  rw [hzero, dotProduct_zero] at h
  have h1 := dotProduct_self_nonneg' (A *ᵥ u)
  have h2 : u ⬝ᵥ u = 0 := by
    have := dotProduct_self_nonneg' u
    nlinarith
  exact hu (dotProduct_self_eq_zero.1 h2)

/-- `ran Bᵀ = ran BᵀB`, in factor form: `Bᵀ = (BᵀB) Q`. -/
theorem exists_transpose_factor {n : ℕ} (B : Matrix (Fin n) (Fin m) ℝ) :
    ∃ Q : Matrix (Fin m) (Fin n) ℝ, Bᵀ = Bᵀ * B * Q := by
  have hle : LinearMap.range (Bᵀ * B).mulVecLin ≤ LinearMap.range Bᵀ.mulVecLin := by
    rw [mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
  have heq : LinearMap.range (Bᵀ * B).mulVecLin = LinearMap.range Bᵀ.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      have h1 := rank_transpose_mul_self B
      have h2 := rank_transpose B
      simp only [rank] at h1 h2
      rw [h1, h2])
  have hcol (j : Fin n) : ∃ q : Fin m → ℝ, (Bᵀ * B) *ᵥ q = Bᵀ *ᵥ Pi.single j 1 := by
    have hmem : Bᵀ *ᵥ Pi.single j 1 ∈ LinearMap.range (Bᵀ * B).mulVecLin := by
      rw [heq]; exact ⟨_, rfl⟩
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq⟩
  choose q hq using hcol
  refine ⟨Matrix.of fun i j => q j i, ?_⟩
  ext i j
  have h := congrFun (hq j) i
  rw [mulVec_single_one] at h
  rw [mul_apply]
  simpa [mulVec, dotProduct] using h.symm

/-- `Aᵀ = (AᵀA)(AᵀA) Q`. -/
theorem exists_sq_factor (A : Matrix (Fin d) (Fin m) ℝ) :
    ∃ Q : Matrix (Fin m) (Fin d) ℝ, Aᵀ = Aᵀ * A * (Aᵀ * A) * Q := by
  obtain ⟨Q₁, hQ₁⟩ := exists_transpose_factor A
  obtain ⟨Q₂, hQ₂⟩ := exists_transpose_factor (Aᵀ * A)
  have hS : (Aᵀ * A)ᵀ = Aᵀ * A := by rw [transpose_mul, transpose_transpose]
  rw [hS] at hQ₂
  refine ⟨Q₂ * Q₁, ?_⟩
  calc Aᵀ = Aᵀ * A * Q₁ := hQ₁
    _ = Aᵀ * A * (Aᵀ * A) * Q₂ * Q₁ := by rw [← hQ₂]
    _ = _ := by rw [Matrix.mul_assoc _ Q₂ Q₁]

/-- `|ε R_ε i j| ≤ 1` for `R_ε = (AᵀA + εI)⁻¹`. -/
theorem abs_smul_inv_gramReg_le (A : Matrix (Fin d) (Fin m) ℝ) {ε : ℝ} (hε : 0 < ε)
    (i j : Fin m) : |ε * (gramReg A ε)⁻¹ i j| ≤ 1 := by
  set u : Fin m → ℝ := (gramReg A ε)⁻¹ *ᵥ Pi.single j 1
  have hu : gramReg A ε *ᵥ u = Pi.single j 1 := by
    simp only [u, mulVec_mulVec, mul_nonsing_inv _ (isUnit_det_gramReg A hε), one_mulVec]
  have hq := dotProduct_gramReg A ε u
  rw [hu, dotProduct_single, mul_one] at hq
  have h1 := dotProduct_self_nonneg' (A *ᵥ u)
  have hs : ε * (u ⬝ᵥ u) ≤ u j := by linarith
  have hj : u j ^ 2 ≤ u ⬝ᵥ u := by
    have := Finset.single_le_sum (f := fun k => u k * u k) (fun k _ => mul_self_nonneg (u k))
      (Finset.mem_univ j)
    simpa [dotProduct, sq] using this
  have hi : u i ^ 2 ≤ u ⬝ᵥ u := by
    have := Finset.single_le_sum (f := fun k => u k * u k) (fun k _ => mul_self_nonneg (u k))
      (Finset.mem_univ i)
    simpa [dotProduct, sq] using this
  have hss : 0 ≤ u ⬝ᵥ u := dotProduct_self_nonneg' u
  have hε2 : ε ^ 2 * (u ⬝ᵥ u) ≤ 1 := by
    rcases eq_or_lt_of_le hss with h0 | hpos
    · rw [← h0]; simp
    · have hj0 : 0 ≤ u j := le_trans (by positivity) hs
      have : (ε * (u ⬝ᵥ u)) ^ 2 ≤ u ⬝ᵥ u := (pow_le_pow_left₀ (by positivity) hs 2).trans hj
      nlinarith
  have hui : u i = (gramReg A ε)⁻¹ i j := by
    simp [u]
  rw [← hui, abs_le]
  constructor <;> nlinarith [sq_nonneg (ε * u i), sq_abs (ε * u i)]

theorem inv_gramReg_mul (A : Matrix (Fin d) (Fin m) ℝ) {ε : ℝ} (hε : 0 < ε) :
    (gramReg A ε)⁻¹ * (Aᵀ * A) = 1 - ε • (gramReg A ε)⁻¹ := by
  have e : (gramReg A ε)⁻¹ * (Aᵀ * A + ε • (1 : Matrix (Fin m) (Fin m) ℝ)) = 1 :=
    nonsing_inv_mul (gramReg A ε) (isUnit_det_gramReg A hε)
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at e
  rw [← e]; abel

theorem tikhonov_eq (A : Matrix (Fin d) (Fin m) ℝ) {ε : ℝ} (hε : 0 < ε)
    {Q : Matrix (Fin m) (Fin d) ℝ} (hQ : Aᵀ = Aᵀ * A * (Aᵀ * A) * Q) :
    tikhonov A ε = Aᵀ * A * Q - ε • Q + ε • ((ε • (gramReg A ε)⁻¹) * Q) := by
  have hRS := inv_gramReg_mul A hε
  rw [tikhonov]
  conv_lhs => rw [hQ]
  calc (gramReg A ε)⁻¹ * (Aᵀ * A * (Aᵀ * A) * Q)
      = ((gramReg A ε)⁻¹ * (Aᵀ * A)) * (Aᵀ * A * Q) := by simp only [Matrix.mul_assoc]
    _ = (1 - ε • (gramReg A ε)⁻¹) * (Aᵀ * A * Q) := by rw [hRS]
    _ = Aᵀ * A * Q - ε • (((gramReg A ε)⁻¹ * (Aᵀ * A)) * Q) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
    _ = Aᵀ * A * Q - ε • ((1 - ε • (gramReg A ε)⁻¹) * Q) := by rw [hRS]
    _ = _ := by rw [Matrix.sub_mul, Matrix.one_mul, smul_sub, Matrix.smul_mul]; abel

/-- **Convergence of the Tikhonov regularizations.** -/
theorem tendsto_tikhonov (A : Matrix (Fin d) (Fin m) ℝ) :
    Tendsto (fun n => tikhonov A (regSeq n)) atTop (𝓝 (pinv A)) := by
  obtain ⟨Q, hQ⟩ := exists_sq_factor A
  have hlim : Tendsto (fun n => tikhonov A (regSeq n)) atTop (𝓝 (Aᵀ * A * Q)) := by
    have he : (fun n => tikhonov A (regSeq n)) = fun n => Aᵀ * A * Q - regSeq n • Q +
        regSeq n • ((regSeq n • (gramReg A (regSeq n))⁻¹) * Q) :=
      funext fun n => tikhonov_eq A (regSeq_pos n) hQ
    rw [he]
    have h1 : Tendsto (fun n => regSeq n • Q) atTop (𝓝 0) := by
      simpa using tendsto_regSeq.smul_const Q
    have h2 : Tendsto (fun n => regSeq n • ((regSeq n • (gramReg A (regSeq n))⁻¹) * Q)) atTop
        (𝓝 0) := by
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      have hb (n : ℕ) : |((regSeq n • (gramReg A (regSeq n))⁻¹) * Q) i j| ≤ ∑ k, |Q k j| := by
        rw [mul_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [abs_mul, Matrix.smul_apply, smul_eq_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (abs_smul_inv_gramReg_le A (regSeq_pos n) i k)
      have hz : Tendsto (fun n => regSeq n * ∑ k, |Q k j|) atTop (𝓝 0) := by
        simpa using tendsto_regSeq.mul_const (∑ k, |Q k j|)
      have hb' (n : ℕ) : ‖(regSeq n • ((regSeq n • (gramReg A (regSeq n))⁻¹) * Q)) i j‖ ≤
          regSeq n * ∑ k, |Q k j| := by
        rw [Matrix.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (regSeq_pos n)]
        exact mul_le_mul_of_nonneg_left (hb n) (regSeq_pos n).le
      exact squeeze_zero_norm hb' hz
    simpa using ((tendsto_const_nhds (x := Aᵀ * A * Q)).sub h1).add h2
  rw [pinv, hlim.limUnder_eq]
  exact hlim

/-- **The four Penrose identities.** -/
theorem isMoorePenrose_pinv (A : Matrix (Fin d) (Fin m) ℝ) : IsMoorePenrose A (pinv A) := by
  set P := pinv A
  have ht := tendsto_tikhonov A
  have hRsymm (ε : ℝ) : ((gramReg A ε)⁻¹)ᵀ = (gramReg A ε)⁻¹ := by
    rw [transpose_nonsing_inv]
    congr 1
    simp [gramReg, transpose_add, transpose_mul]
  have hPA (ε : ℝ) (hε : 0 < ε) : tikhonov A ε * A = 1 - ε • (gramReg A ε)⁻¹ := by
    rw [tikhonov, Matrix.mul_assoc]; exact inv_gramReg_mul A hε
  have hcont_l : Tendsto (fun n => A * tikhonov A (regSeq n) * A) atTop (𝓝 (A * P * A)) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).continuousAt.tendsto.comp ht
  have hAPA : A * P * A = A := by
    have he (n : ℕ) : A * tikhonov A (regSeq n) * A = A - regSeq n • (tikhonov A (regSeq n))ᵀ := by
      rw [Matrix.mul_assoc, hPA _ (regSeq_pos n), Matrix.mul_sub, Matrix.mul_one,
        Matrix.mul_smul, tikhonov, transpose_mul, transpose_transpose, hRsymm]
    have h2 : Tendsto (fun n => A - regSeq n • (tikhonov A (regSeq n))ᵀ) atTop (𝓝 A) := by
      have : Tendsto (fun n => regSeq n • (tikhonov A (regSeq n))ᵀ) atTop (𝓝 0) := by
        simpa using tendsto_regSeq.smul ((continuous_id.matrix_transpose).continuousAt.tendsto.comp ht)
      simpa using (tendsto_const_nhds (x := A)).sub this
    exact tendsto_nhds_unique (hcont_l.congr he) h2
  have hsymmAP : (A * P)ᵀ = A * P := by
    have h1 : Tendsto (fun n => (A * tikhonov A (regSeq n))ᵀ) atTop (𝓝 ((A * P)ᵀ)) :=
      ((continuous_const.matrix_mul continuous_id).matrix_transpose).continuousAt.tendsto.comp ht
    have h2 : Tendsto (fun n => A * tikhonov A (regSeq n)) atTop (𝓝 (A * P)) :=
      (continuous_const.matrix_mul continuous_id).continuousAt.tendsto.comp ht
    have he (n : ℕ) : (A * tikhonov A (regSeq n))ᵀ = A * tikhonov A (regSeq n) := by
      rw [tikhonov, transpose_mul, transpose_mul, transpose_transpose, hRsymm, Matrix.mul_assoc]
    exact tendsto_nhds_unique (h1.congr he) h2
  have hsymmPA : (P * A)ᵀ = P * A := by
    have h1 : Tendsto (fun n => (tikhonov A (regSeq n) * A)ᵀ) atTop (𝓝 ((P * A)ᵀ)) :=
      ((continuous_id.matrix_mul continuous_const).matrix_transpose).continuousAt.tendsto.comp ht
    have h2 : Tendsto (fun n => tikhonov A (regSeq n) * A) atTop (𝓝 (P * A)) :=
      (continuous_id.matrix_mul continuous_const).continuousAt.tendsto.comp ht
    have he (n : ℕ) : (tikhonov A (regSeq n) * A)ᵀ = tikhonov A (regSeq n) * A := by
      rw [hPA _ (regSeq_pos n), transpose_sub, transpose_one, transpose_smul, hRsymm]
    exact tendsto_nhds_unique (h1.congr he) h2
  -- `Aᵀ = AᵀA P`
  have hAt : Aᵀ = Aᵀ * A * P := by
    have h := congrArg Matrix.transpose hAPA
    rw [transpose_mul, transpose_mul] at h
    calc Aᵀ = Aᵀ * (Pᵀ * Aᵀ) := h.symm
      _ = Aᵀ * (A * P)ᵀ := by rw [transpose_mul]
      _ = Aᵀ * (A * P) := by rw [hsymmAP]
      _ = _ := by rw [Matrix.mul_assoc]
  have hPAP : P * A * P = P := by
    have h1 : Tendsto (fun n => tikhonov A (regSeq n) * A * P) atTop (𝓝 (P * A * P)) :=
      ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_const).continuousAt.tendsto.comp ht
    have he (n : ℕ) : tikhonov A (regSeq n) * A * P = tikhonov A (regSeq n) := by
      rw [tikhonov, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, ← hAt]
    exact tendsto_nhds_unique (h1.congr he) ht
  exact ⟨hAPA, hPAP, hsymmAP, hsymmPA⟩

/-- Every entry of `A ↦ P_ε(A)` is continuous (`ε > 0`). -/
theorem continuous_tikhonov_entry' {ε : ℝ} (hε : 0 < ε) (k : Fin m) (i : Fin d) :
    Continuous fun A : Matrix (Fin d) (Fin m) ℝ => tikhonov A ε k i := by
  have hG : Continuous fun A : Matrix (Fin d) (Fin m) ℝ => gramReg A ε :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).add continuous_const
  have hinv : Continuous fun A : Matrix (Fin d) (Fin m) ℝ => (gramReg A ε)⁻¹ := by
    have he : (fun A : Matrix (Fin d) (Fin m) ℝ => (gramReg A ε)⁻¹) =
        fun A => ((gramReg A ε).det)⁻¹ • (gramReg A ε).adjugate := by
      funext A; rw [inv_def, Ring.inverse_eq_inv]
    rw [he]
    exact (hG.matrix_det.inv₀ fun A => (isUnit_det_gramReg A hε).ne_zero).smul
      hG.matrix_adjugate
  exact ((hinv.matrix_mul continuous_id.matrix_transpose).matrix_elem k i)

/-- The same on the coordinate space `Fin d → Fin m → ℝ`. -/
theorem continuous_tikhonov_entry {ε : ℝ} (hε : 0 < ε) (k : Fin m) (i : Fin d) :
    Continuous fun A : Fin d → Fin m → ℝ => tikhonov (Matrix.of A) ε k i :=
  (continuous_tikhonov_entry' hε k i).comp
    (continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i))

/-- **Borel measurability of the pseudoinverse selector**: for `σ : X → ℝ^{d×m}` with measurable
entries, every entry of `x ↦ σ(x)⁺` is measurable. -/
theorem measurable_pinv_comp {X : Type*} [MeasurableSpace X]
    {σ : X → Matrix (Fin d) (Fin m) ℝ} (hσ : ∀ i j, Measurable fun x => σ x i j)
    (k : Fin m) (i : Fin d) : Measurable fun x => pinv (σ x) k i := by
  have hσ' : Measurable fun x => (fun i j => σ x i j : Fin d → Fin m → ℝ) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hσ i j
  refine measurable_of_tendsto_metrizable (f := fun n x => tikhonov (σ x) (regSeq n) k i)
    (fun n => by
      exact ((continuous_tikhonov_entry (regSeq_pos n) k i).measurable).comp hσ') ?_
  refine tendsto_pi_nhds.2 fun x => ?_
  have h := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (tendsto_tikhonov (σ x)) k) i
  exact h

end BlockBand.SourceProcess.Stochastic.Representation
