module

public import BlockBand.Endpoints.Response.ClockEntranceJensenDefs
public import BlockBand.Endpoints.Response.ClockEntranceJensenEvent

/-!
# The one-layer Jensen gap from the matrix Taylor step

This file proves `ClockLayerJensenGap` from the fractional-trace Taylor step
`FractionalTraceJensenGap`, the passive covariance gap and the one-port inputs
(`clockLayerJensenGap_of_taylor`), and from it the finite fractional entrance of the near clock
(`clockFractionalEntrance_of_onePortProps`).

The auxiliary matrix facts are:
* `cej_norm_entry_le`: `|M_ac| ≤ ‖M‖` (Euclidean operator norm).
* `cej_sqrt` and its lemmas: `A^{1/2} = V diag(√λ) V*` in the eigenbasis `V` of `A ⪰ 0`.
* `cej_matrixExpect_sandwich`: `E(SUS') = S (EU) S'` for integrable entries.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionLaws

section Helpers

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An entry is bounded by the Euclidean operator norm: `|M_ac| ≤ ‖M‖`. -/
theorem cej_norm_entry_le (M : Matrix n n ℂ) (a c : n) : ‖M a c‖ ≤ ‖M‖ := by
  have h := l2_opNorm_mulVec M (EuclideanSpace.single c 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ a).trans h)
  simp [EuclideanSpace.single]

/-- `A^{1/2} = V diag(√λ) V*` for `A ⪰ 0`, `V` the eigenvector unitary of `A`. -/
def cej_sqrt {A : Matrix n n ℂ} (hA : A.PosSemidef) : Matrix n n ℂ :=
  (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
    diagonal (fun i => ((Real.sqrt (hA.isHermitian.eigenvalues i) : ℝ) : ℂ)) *
      star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)

theorem cej_spectral {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  have := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  exact this

theorem cej_sqrt_conjTranspose {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (cej_sqrt hA)ᴴ = cej_sqrt hA := by
  unfold cej_sqrt
  rw [conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose, ← star_eq_conjTranspose,
    star_star, ← star_eq_conjTranspose, Matrix.mul_assoc]
  congr 3
  funext i
  simp [Pi.star_apply]

theorem cej_star_V_mul_sqrt {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * cej_sqrt hA =
      diagonal (fun i => ((Real.sqrt (hA.isHermitian.eigenvalues i) : ℝ) : ℂ)) *
        star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) := by
  unfold cej_sqrt
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mem_unitaryGroup_iff'.mp hA.isHermitian.eigenvectorUnitary.2, Matrix.one_mul]

theorem cej_sqrt_mul_V {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    cej_sqrt hA * (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) =
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => ((Real.sqrt (hA.isHermitian.eigenvalues i) : ℝ) : ℂ)) := by
  unfold cej_sqrt
  rw [Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.mp hA.isHermitian.eigenvectorUnitary.2,
    Matrix.mul_one]

theorem cej_sqrt_mul_self {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    cej_sqrt hA * cej_sqrt hA = A := by
  set V := (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  set D := diagonal (fun i => ((Real.sqrt (hA.isHermitian.eigenvalues i) : ℝ) : ℂ))
  have hVV : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.isHermitian.eigenvectorUnitary.2
  calc cej_sqrt hA * cej_sqrt hA = V * D * (star V * V) * D * star V := by
        simp only [cej_sqrt, V, D, Matrix.mul_assoc]
    _ = V * (D * D) * star V := by rw [hVV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = A := by
        conv_rhs => rw [cej_spectral hA.isHermitian]
        simp only [D, diagonal_mul_diagonal]
        congr 3
        funext i
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hA.eigenvalues_nonneg i)]

omit [DecidableEq n] in
/-- `E(S U S') = S (E U) S'` for a random matrix with integrable entries. -/
theorem cej_matrixExpect_sandwich {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : Ω → Matrix n n ℂ} (hU : ∀ a b, Integrable (fun ω => U ω a b) μ) (S S' : Matrix n n ℂ) :
    matrixExpect μ (fun ω => S * U ω * S') = S * matrixExpect μ U * S' := by
  ext a c
  simp only [matrixExpect, Matrix.of_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ fun l _ => ?_]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const, integral_finsetSum _ fun k _ => (hU k l).const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
  · exact (integrable_finsetSum _ fun k _ => (hU k l).const_mul _).mul_const _

end Helpers

variable {W : ℕ}

/-- `ν ↦ freshU b E X ν = LL*` is measurable. -/
theorem cej_measurable_freshU (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable fun ν : LayerSample W .oneBlockOnePort => freshU b E X ν := by
  have hLm := cel_measurable_freshL b E X
  unfold freshU
  exact (Continuous.matrix_mul continuous_fst
    (continuous_snd.matrix_conjTranspose)).measurable.comp (hLm.prodMk hLm)

/-- The entries of `U = LL*` are integrable once `E‖L‖² < ∞` (`|U_ac| ≤ ‖U‖ ≤ ‖L‖²`). -/
theorem cej_integrable_freshU {b E C : ℝ} {X : Matrix (Fin W) (Fin W) ℂ}
    (hL2 : ∫⁻ ν, ENNReal.ofReal (‖freshL b E X ν‖ ^ 2) ∂freshLaw W b ≤ ENNReal.ofReal C)
    (a c : Fin W) : Integrable (fun ν => freshU b E X ν a c) (freshLaw W b) := by
  have hLm := cel_measurable_freshL b E X
  have hg : Integrable (fun ν => ‖freshL b E X ν‖ ^ 2) (freshLaw W b) := by
    refine ⟨((continuous_norm.measurable.comp hLm).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ν => by positivity)]
    exact lt_of_le_of_lt hL2 ENNReal.ofReal_lt_top
  refine Integrable.mono' hg
    ((measurable_pi_apply c).comp ((measurable_pi_apply a).comp
      (cej_measurable_freshU b E X))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ν => ?_)
  calc ‖freshU b E X ν a c‖ ≤ ‖freshU b E X ν‖ := cej_norm_entry_le _ a c
    _ ≤ ‖freshL b E X ν‖ * ‖(freshL b E X ν)ᴴ‖ := l2_opNorm_mul _ _
    _ = ‖freshL b E X ν‖ ^ 2 := by rw [l2_opNorm_conjTranspose, sq]

/-- `Tr(S·LL*·S)^p = Tr(L*AL)^p` when `S·S = A`. -/
theorem cej_fracTrace_sandwich (p : ℝ) {A S L : Matrix (Fin W) (Fin W) ℂ} (hS : S * S = A) :
    fracTrace p (S * (L * Lᴴ) * S) = fracTrace p (Lᴴ * A * L) := by
  rw [show S * (L * Lᴴ) * S = (S * L) * (Lᴴ * S) by simp only [Matrix.mul_assoc],
    fracTrace_mul_comm, ← hS]
  simp only [Matrix.mul_assoc]

/-- `Tr(S·U·S)^p = Tr(UA)^p` when `S·S = A`. -/
theorem cej_fracTrace_sandwich' (p : ℝ) {A S U : Matrix (Fin W) (Fin W) ℂ} (hS : S * S = A) :
    fracTrace p (S * U * S) = fracTrace p (U * A) := by
  rw [Matrix.mul_assoc, fracTrace_mul_comm, ← hS, Matrix.mul_assoc]

/-- The entries of the `A^{1/2}`-sandwich in the eigenbasis of `A`:
`(V*·SMS·V)_ij = √λ_i (V*MV)_ij √λ_j`. -/
theorem cej_sandwich_entry {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.PosSemidef)
    (M : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) :
    (star (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) *
        (cej_sqrt hA * M * cej_sqrt hA) * (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)) i j =
      ((Real.sqrt (hA.isHermitian.eigenvalues i) : ℝ) : ℂ) *
        (star (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) * M *
          (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)) i j *
        ((Real.sqrt (hA.isHermitian.eigenvalues j) : ℝ) : ℂ) := by
  have e : star (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) *
      (cej_sqrt hA * M * cej_sqrt hA) * (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) =
      (star (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) * cej_sqrt hA) * M *
        (cej_sqrt hA * (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)) := by
    simp only [Matrix.mul_assoc]
  rw [e, cej_star_V_mul_sqrt, cej_sqrt_mul_V]
  rw [show diagonal (fun i => ((Real.sqrt (hA.isHermitian.eigenvalues i) : ℝ) : ℂ)) *
      star (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) * M *
      ((hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) *
        diagonal (fun i => ((Real.sqrt (hA.isHermitian.eigenvalues i) : ℝ) : ℂ))) =
      diagonal (fun i => ((Real.sqrt (hA.isHermitian.eigenvalues i) : ℝ) : ℂ)) *
      (star (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) * M *
        (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)) *
        diagonal (fun i => ((Real.sqrt (hA.isHermitian.eigenvalues i) : ℝ) : ℂ)) by
    simp only [Matrix.mul_assoc]]
  rw [mul_diagonal, diagonal_mul]

/-- **`ClockLayerJensenGap` from the matrix Taylor step.**
Inputs: `PassiveCovarianceContract`, `TransmissionLawContract` (`jetGap`) and
`PassiveSourceMixingContract` (`oneStepFluctuation`, `p = 4`); the one-port inputs
`OnePortPassiveMean` and `OnePortOperatorMoments` (`r = 1, 2`); and the Taylor step
`FractionalTraceJensenGap`, applied with `B = A^{1/2}LL*A^{1/2}`, `Q = K₀²A` (eigenbasis of `A`,
`q = K₀²λ`) on the retained event `‖L‖ ≤ K₀`. The constants are `K = K₀²`, `c = c_T κ`
(`c_T` of the Taylor step, `κ` of `cej_event_gap`).
-/
theorem clockLayerJensenGap_of_taylor (hPC : PassiveCovarianceContract)
    (hTL : TransmissionLawContract) (hPSM : PassiveSourceMixingContract)
    (hTay : FractionalTraceJensenGap) (hMean : OnePortPassiveMean)
    (hOp : OnePortOperatorMoments) : ClockLayerJensenGap := by
  intro b hb0 hb1 E hE1 hE2 p hp0 hp1 s hs
  obtain ⟨κ, d₁, Kmin, W₁, hκ, hd₁, hKmin, hEv⟩ :=
    cej_event_gap hPC hTL hPSM hOp hb0 hb1 hE1 hE2 hs
  obtain ⟨Ca, da, Wa, hCa, hda, hMa⟩ := hMean b hb0 hb1 E hE1 hE2 s hs
  obtain ⟨db, hdb, hOpb⟩ := hOp b hb0 hb1 E hE1 hE2 s hs
  obtain ⟨C1, Wb, hC1⟩ := hOpb 1
  obtain ⟨cT, hcT, hT⟩ := hTay p hp0 hp1
  set K₀ := max Kmin (1 + 2 * Ca)
  have hK₀1 : 1 ≤ K₀ := le_trans (by linarith) (le_max_right _ _)
  have hK₀0 : 0 < K₀ := by linarith
  have hK₀min : Kmin ≤ K₀ := le_max_left _ _
  set d := min (min d₁ da) (min db 1)
  refine ⟨K₀ ^ 2, cT * κ, d, max (max W₁ Wa) (max Wb 1), by positivity, by positivity,
    lt_min (lt_min hd₁ hda) (lt_min hdb one_pos), ?_⟩
  intro W hW X hX A hA
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWa : Wa ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWb : Wb ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWge : (1 : ℝ) ≤ W := by
    have : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
    exact_mod_cast this
  have hWpos : (0 : ℝ) < W := by linarith
  have hX1 : cel_InJetDomain b E s d₁ X := hX.mono ((min_le_left _ _).trans (min_le_left _ _))
  have hXa : cel_InJetDomain b E s da X := hX.mono ((min_le_left _ _).trans (min_le_right _ _))
  have hXb : cel_InJetDomain b E s db X := hX.mono ((min_le_right _ _).trans (min_le_left _ _))
  have hd1 : d ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have := cel_isProbabilityMeasure_freshLaw W b
  set μ := freshLaw W b
  set V := (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
  set lam := hA.isHermitian.eigenvalues
  set Sq := cej_sqrt hA
  set Ubar := matrixExpect μ (freshU b E X)
  set B : LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ :=
    fun ν => Sq * freshU b E X ν * Sq
  set G : Set (LayerSample W .oneBlockOnePort) := {ν | ‖freshL b E X ν‖ ≤ K₀}
  have hLm := cel_measurable_freshL b E X
  have hGm : MeasurableSet G :=
    measurableSet_le (continuous_norm.measurable.comp hLm) measurable_const
  -- integrability
  have hL2 : ∫⁻ ν, ENNReal.ofReal (‖freshL b E X ν‖ ^ 2) ∂μ ≤ ENNReal.ofReal C1 := by
    have := hC1 W hWb X hXb
    rwa [mul_one] at this
  have hUint := cej_integrable_freshU hL2
  have hBint : ∀ a c, Integrable (fun ν => B ν a c) μ := by
    intro a c
    simp only [B, Matrix.mul_apply]
    exact integrable_finsetSum _ fun l _ =>
      (integrable_finsetSum _ fun k _ => (hUint k l).const_mul _).mul_const _
  have hBbar : matrixExpect μ B = Sq * Ubar * Sq := cej_matrixExpect_sandwich hUint Sq Sq
  have hSh : Sqᴴ = Sq := cej_sqrt_conjTranspose hA
  have hSS : Sq * Sq = A := cej_sqrt_mul_self hA
  have hBpsd : ∀ ν, (B ν).PosSemidef := fun ν => by
    have := (posSemidef_self_mul_conjTranspose (freshL b E X ν)).mul_mul_conjTranspose_same Sq
    rw [hSh] at this
    exact this
  -- the comparison matrix `Q = K₀² A`
  set q : Fin W → ℝ := fun i => K₀ ^ 2 * lam i
  have hq0 : ∀ i, 0 ≤ q i := fun i => mul_nonneg (by positivity) (hA.eigenvalues_nonneg i)
  have hQ : V * diagonal (fun i => ((q i : ℝ) : ℂ)) * star V =
      Sq * ((((K₀ ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) * Sq := by
    have hd : diagonal (fun i => ((q i : ℝ) : ℂ)) =
        (((K₀ ^ 2 : ℝ)) : ℂ) • diagonal (fun i => ((lam i : ℝ) : ℂ)) := by
      rw [← diagonal_smul]
      congr 1
      funext i
      simp [q]
    rw [hd, Matrix.mul_smul, Matrix.smul_mul, ← cej_spectral hA.isHermitian, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, hSS]
  have hsand : ∀ M N : Matrix (Fin W) (Fin W) ℂ, (M - N).PosSemidef →
      (Sq * M * Sq - Sq * N * Sq).PosSemidef := fun M N h => by
    have := h.mul_mul_conjTranspose_same Sq
    rwa [hSh, Matrix.mul_sub, Matrix.sub_mul] at this
  have hmean := hMa W hWa X hXa
  have hm : 1 + Ca * jetDistance0 b E X + Ca / (W : ℝ) ^ 2 ≤ K₀ ^ 2 := by
    have h1 : jetDistance0 b E X ≤ 1 := le_trans hX.2.1 hd1
    have h2 : Ca / (W : ℝ) ^ 2 ≤ Ca := div_le_self hCa (by nlinarith)
    have h3 : 1 + 2 * Ca ≤ K₀ := le_max_right _ _
    have h4 : K₀ ≤ K₀ ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hCa]
  have hQB : (V * diagonal (fun i => ((q i : ℝ) : ℂ)) * star V - matrixExpect μ B).PosSemidef := by
    rw [hQ, hBbar]
    refine hsand _ _ ?_
    have e : (((K₀ ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - Ubar =
        (((K₀ ^ 2 - (1 + Ca * jetDistance0 b E X + Ca / (W : ℝ) ^ 2) : ℝ)) : ℂ) •
            (1 : Matrix (Fin W) (Fin W) ℂ) +
          ((((1 + Ca * jetDistance0 b E X + Ca / (W : ℝ) ^ 2 : ℝ)) : ℂ) •
            (1 : Matrix (Fin W) (Fin W) ℂ) - Ubar) := by
      rw [Complex.ofReal_sub, sub_smul]
      abel
    rw [e]
    refine (PosSemidef.one.smul ?_).add hmean.2
    exact Complex.zero_le_real.mpr (by linarith)
  have hQBG : ∀ ν ∈ G,
      (V * diagonal (fun i => ((q i : ℝ) : ℂ)) * star V - B ν).PosSemidef := by
    intro ν hν
    rw [hQ]
    exact hsand _ _ (posSemidef_sq_smul_one_sub_of_norm_le _ hK₀0.le hν)
  have key := hT W (LayerSample W .oneBlockOnePort) μ inferInstance B V q G hBpsd hBint hGm
    hA.isHermitian.eigenvectorUnitary.2 hq0 hQB hQBG
  -- the left trace
  have hK1 : ∫⁻ ν, ENNReal.ofReal (fracTrace p (B ν)) ∂μ =
      ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν)) ∂μ :=
    lintegral_congr fun ν => by
      simp only [B, freshU]
      rw [cej_fracTrace_sandwich p hSS]
  -- the right trace
  have hK2 : fracTrace p (matrixExpect μ B) = fracTrace p (Ubar * A) := by
    rw [hBbar, cej_fracTrace_sandwich' p hSS]
  -- the kernel sum
  set k : Fin W → Fin W → ℝ := fun i j =>
    ∫ t in Set.Ioi (0 : ℝ), concavityKernel p (q i) (q j) t
  have hk0 : ∀ i j, 0 ≤ k i j := fun i j =>
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      concavityKernel_nonneg (hq0 i) (hq0 j) (le_of_lt ht)
  set x : Fin W → Fin W → LayerSample W .oneBlockOnePort → ℂ := fun i j ν =>
    (star V * (freshU b E X ν - Ubar) * V) i j
  have hxm : ∀ i j, Measurable (x i j) := fun i j => by
    have : Measurable fun ν => star V * (freshU b E X ν - Ubar) * V :=
      ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul
        continuous_const).measurable.comp (cej_measurable_freshU b E X)
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp this)
  have hentry : ∀ ν i j, ‖(star V * (B ν - matrixExpect μ B) * V) i j‖ ^ 2 =
      lam i * lam j * ‖x i j ν‖ ^ 2 := fun ν i j => by
    have e : B ν - matrixExpect μ B = Sq * (freshU b E X ν - Ubar) * Sq := by
      rw [hBbar, Matrix.mul_sub, Matrix.sub_mul]
    rw [e, cej_sandwich_entry hA, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, mul_pow, Real.sq_sqrt (hA.eigenvalues_nonneg i),
      Real.sq_sqrt (hA.eigenvalues_nonneg j)]
    ring
  set R := cel_retained b E X hA.isHermitian
  have hgapR : cel_retainedGap b E p (K₀ ^ 2) X hA.isHermitian =
      ∑ i ∈ R, ∑ j ∈ R, lam i * lam j * k i j := rfl
  have hpt : ∀ ν, ∑ i ∈ R, ∑ j ∈ R, lam i * lam j * k i j * ‖x i j ν‖ ^ 2 ≤
      ∑ i, ∑ j, ‖(star V * (B ν - matrixExpect μ B) * V) i j‖ ^ 2 * k i j := fun ν => by
    simp only [hentry]
    have hnn : ∀ i j, 0 ≤ lam i * lam j * k i j * ‖x i j ν‖ ^ 2 := fun i j =>
      mul_nonneg (mul_nonneg (mul_nonneg (hA.eigenvalues_nonneg i) (hA.eigenvalues_nonneg j))
        (hk0 i j)) (by positivity)
    calc ∑ i ∈ R, ∑ j ∈ R, lam i * lam j * k i j * ‖x i j ν‖ ^ 2
        ≤ ∑ i ∈ R, ∑ j, lam i * lam j * k i j * ‖x i j ν‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) fun j _ _ => hnn i j
      _ ≤ ∑ i, ∑ j, lam i * lam j * k i j * ‖x i j ν‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
            Finset.sum_nonneg fun j _ => hnn i j
      _ = _ := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
  have hK3 : ENNReal.ofReal (cT * κ / W * cel_retainedGap b E p (K₀ ^ 2) X hA.isHermitian) ≤
      ENNReal.ofReal cT * ∫⁻ ν in G, ENNReal.ofReal (∑ i, ∑ j,
        ‖(star V * (B ν - matrixExpect μ B) * V) i j‖ ^ 2 * k i j) ∂μ := by
    have hnn : ∀ i j, 0 ≤ lam i * lam j * k i j := fun i j =>
      mul_nonneg (mul_nonneg (hA.eigenvalues_nonneg i) (hA.eigenvalues_nonneg j)) (hk0 i j)
    have hlow : ∑ i ∈ R, ∑ j ∈ R, ENNReal.ofReal (lam i * lam j * k i j) *
          ENNReal.ofReal (κ / W) ≤
        ∫⁻ ν in G, ENNReal.ofReal (∑ i ∈ R, ∑ j ∈ R,
          lam i * lam j * k i j * ‖x i j ν‖ ^ 2) ∂μ := by
      have hsum : ∀ ν, ENNReal.ofReal (∑ i ∈ R, ∑ j ∈ R, lam i * lam j * k i j * ‖x i j ν‖ ^ 2) =
          ∑ i ∈ R, ∑ j ∈ R, ENNReal.ofReal (lam i * lam j * k i j) *
            ENNReal.ofReal (‖x i j ν‖ ^ 2) := fun ν => by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (hnn i j) (by positivity)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hnn i j) (by positivity)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_mul (hnn i j)]
      simp_rw [hsum]
      have hmij : ∀ i j, Measurable fun ν => ENNReal.ofReal (lam i * lam j * k i j) *
          ENNReal.ofReal (‖x i j ν‖ ^ 2) := fun i j =>
        (ENNReal.measurable_ofReal.comp ((continuous_norm.measurable.comp (hxm i j)).pow_const
          2)).const_mul _
      rw [lintegral_finsetSum R fun i _ => Finset.measurable_sum R fun j _ => hmij i j]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [lintegral_finsetSum R fun j _ => hmij i j]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      exact hEv W hW1 X hX1 K₀ hK₀min V hA.isHermitian.eigenvectorUnitary.2 i j
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    have hleft : ENNReal.ofReal (cT * κ / W * cel_retainedGap b E p (K₀ ^ 2) X hA.isHermitian) =
        ENNReal.ofReal cT * ∑ i ∈ R, ∑ j ∈ R, ENNReal.ofReal (lam i * lam j * k i j) *
          ENNReal.ofReal (κ / W) := by
      have h1 : ∑ i ∈ R, ∑ j ∈ R, ENNReal.ofReal (lam i * lam j * k i j) *
          ENNReal.ofReal (κ / W) =
          ENNReal.ofReal ((∑ i ∈ R, ∑ j ∈ R, lam i * lam j * k i j) * (κ / W)) := by
        rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn i j),
          ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn i j,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => hnn i j, Finset.sum_mul]
      rw [hgapR, h1, ← ENNReal.ofReal_mul hcT.le]
      congr 1
      ring
    rw [hleft]
    gcongr ENNReal.ofReal cT * ?_
    refine hlow.trans (setLIntegral_mono' hGm fun ν _ => ENNReal.ofReal_le_ofReal (hpt ν))
  rw [hK1, hK2] at key
  calc ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν)) ∂μ +
        ENNReal.ofReal (cT * κ / W * cel_retainedGap b E p (K₀ ^ 2) X hA.isHermitian)
      ≤ ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν)) ∂μ +
        ENNReal.ofReal cT * ∫⁻ ν in G, ENNReal.ofReal (∑ i, ∑ j,
          ‖(star V * (B ν - matrixExpect μ B) * V) i j‖ ^ 2 * k i j) ∂μ := by gcongr
    _ ≤ ENNReal.ofReal (fracTrace p (Ubar * A)) := key

open BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.Inputs in

/-- **`ClockFractionalEntranceContract` from the one-port inputs and the Taylor step.** The
hypotheses are `EdgeClockMomentsContract`, `TransmissionLengthUniformContract`,
`ConditionalBlockGUECount`, `TransmissionLawContract`, `PassiveCovarianceContract`,
`PassiveSourceMixingContract`, the one-port inputs `OnePortPassiveMean`, `OnePortOperatorMoments`,
`OnePortJetContraction`, and the model-free matrix inequality `FractionalTraceJensenGap`. -/
theorem clockFractionalEntrance_of_onePortProps (hECM : EdgeClockMomentsContract)
    (hTLU : BlockBand.Internal.Contracts.TransmissionUniform.TransmissionLengthUniformContract)
    (hCount : ConditionalBlockGUECount) (hTL : TransmissionLawContract)
    (hPC : PassiveCovarianceContract) (hPSM : PassiveSourceMixingContract)
    (hTay : FractionalTraceJensenGap) (hMean : OnePortPassiveMean)
    (hOp : OnePortOperatorMoments) (hJet : OnePortJetContraction) :
    ClockFractionalEntranceContract :=
  clockFractionalEntrance_of_jensenGap hECM hTLU hCount hTL
    (clockLayerJensenGap_of_taylor hPC hTL hPSM hTay hMean hOp) hMean hOp hJet

end BlockBand.Endpoints
