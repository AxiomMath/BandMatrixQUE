module

public import BlockBand.Palm.MomentFlow.LocalScaling
public import BlockBand.Palm.MomentFlow.LocalMDE
public import BlockBand.Palm.MomentFlow.BridgeIdentity

/-!
# The external local law along the flow, and `X_i ≤ 2Nη Im q*Gq`

*Deterministic part* (every Hermitian `H` with simple spectrum, `N ≥ 1`):
* `measurable_matrix_inv`; `sourceResolvent_eq` (`sourceResolvent (√σ) F W z` is
  `(F + √σ W - z)⁻¹`); `isotropicControl_self` (the isotropic control at `x = y = q` is
  `√(ρ/(N|Im z|)) |q* Γ_M q|`).
* `overlap_le_of_near`: if `|x - λ_i| ≤ η`, `η > 0`, then
  `X_i = N|q* u_i|² ≤ 2Nη · Im q*(H - x - iη)⁻¹ q` (from the spectral identity, all terms `≥ 0`);
  `im_quad_le`: `Im q*Gq ≤ Im q*Mq + |q*(G - M)q|`. So `X_i` is controlled through `Im q*Gq`, never
  through `|q*Mq|`.

*Probabilistic part* (measure `flowLaw N a`, `0 ≤ a ≤ σ`, `0 < σ`):
* `flowLaw_isotropicBad_eq`, `flowLaw_averagedBad_eq`: the bad events of the external local law
  for `F + √σ W` under `gueSourceLaw N` are exactly the bad events of `flowMatrix F a ω σ` under
  `flowLaw N a`.
* `flowLaw_isotropicBad_le`, `flowLaw_averagedBad_le`: from `ExternalLocalGUE` at every `z` of the
  local-law domain; with `MDEBranchIdentification` (`flowLaw_isotropicBad_freshM_le`) the branch
  matrix is `freshM F σ z`.
* `overlap_bound_on_grid`: union bound over a deterministic finite grid `X` of energies at height
  `η`: off an event of probability `≤ |X| N^{-D}`, every eigenvalue `λ_i(σ)` within `η` of the grid
  has `X_i(σ) ≤ 2Nη (Im q*M(x+iη)q + N^δ · isotropicControl)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.External
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

variable {N : ℕ}

/-!
## Deterministic layer
-/

theorem measurable_matrix_inv :
    Measurable (fun A : Matrix (Fin N) (Fin N) ℂ => A⁻¹) := by
  apply Measurable.of_eval_matrix
  intro i j
  have hdet : Measurable (fun A : Matrix (Fin N) (Fin N) ℂ => A.det) :=
    continuous_id.matrix_det.measurable
  have hadj : Measurable (fun A : Matrix (Fin N) (Fin N) ℂ => A.adjugate i j) :=
    (measurable_matrixEntry i j).comp continuous_id.matrix_adjugate.measurable
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact hdet.inv.mul hadj

theorem sourceResolvent_eq {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (σ : ℝ)
    (W : CEH.SourceHermitian N) (z : ℂ) :
    CEH.sourceResolvent (Real.sqrt σ) ⟨F, hF⟩ W z =
      (F + ((Real.sqrt σ : ℝ) : ℂ) • W.1 - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := rfl

theorem isotropicControl_self (M : CEH.SourceMatrix N) (z : ℂ) (q : Fin N → ℂ) :
    CEH.isotropicControl M z q q =
      Real.sqrt (CEH.sourceDensity M / ((N : ℝ) * |z.im|)) *
        |(CEH.sourceMatrixElement (CEH.gammaMatrix M) q q).re| := by
  unfold CEH.isotropicControl
  set a := (CEH.sourceMatrixElement (CEH.gammaMatrix M) q q).re
  set n := CEH.sourceVectorNorm q
  by_cases hn : n = 0
  · have hq : q = 0 := by
      have h0 : ∑ k, ‖q k‖ ^ 2 = 0 := by
        have := Real.sqrt_eq_zero'.1 hn
        exact le_antisymm this (Finset.sum_nonneg fun _ _ => by positivity)
      funext k
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 h0 k
        (Finset.mem_univ k)
      simpa using this
    subst hq
    simp [a, CEH.sourceMatrixElement]
  · rw [mul_assoc, mul_assoc]
    congr 1
    have hn2 : n ^ 2 * n ^ 2 ≠ 0 := by positivity
    rw [show a * a / (n ^ 2 * n ^ 2) = (|a| / n ^ 2) ^ 2 by
      rw [div_pow, ← pow_mul, sq_abs]; ring, Real.sqrt_sq (by positivity)]
    field_simp

/-- `Im q*Gq ≤ Im q*Mq + |q*(G - M)q|`. -/
theorem im_quad_le (G M : Matrix (Fin N) (Fin N) ℂ) (q : Fin N → ℂ) :
    (star q ⬝ᵥ (G *ᵥ q)).im ≤ (star q ⬝ᵥ (M *ᵥ q)).im + ‖star q ⬝ᵥ ((G - M) *ᵥ q)‖ := by
  have h : star q ⬝ᵥ (G *ᵥ q) = star q ⬝ᵥ (M *ᵥ q) + star q ⬝ᵥ ((G - M) *ᵥ q) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]; ring
  rw [h, Complex.add_im]
  linarith [Complex.im_le_norm (star q ⬝ᵥ ((G - M) *ᵥ q))]

/-- If `|x - λ_i| ≤ η`, then `X_i ≤ 2Nη · Im q*(H - x - iη)⁻¹ q`. -/
theorem overlap_le_of_near {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) (hN : 0 < N) {x η : ℝ} (hη : 0 < η) (q : Fin N → ℂ)
    (i : Fin N) (hx : |freshEigenvalue H i - x| ≤ η) :
    (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector H i‖ ^ 2 ≤
      2 * N * η * (star q ⬝ᵥ ((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im := by
  rw [← resolvent_im_spectral hH hs hN x hη.ne' q]
  set X : Fin N → ℝ := fun j => (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector H j‖ ^ 2
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ j, 0 ≤ η / ((freshEigenvalue H j - x) ^ 2 + η ^ 2) * X j := fun j => by
    positivity
  have hsingle := Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
  have hden : (freshEigenvalue H i - x) ^ 2 + η ^ 2 ≤ 2 * η ^ 2 := by
    have := sq_le_sq' (abs_le.1 hx).1 (abs_le.1 hx).2
    nlinarith [this]
  have hXi : 0 ≤ X i := by positivity
  have hlow : X i / (2 * η) ≤ η / ((freshEigenvalue H i - x) ^ 2 + η ^ 2) * X i := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hden, hXi, hη]
  have key : X i / (2 * η) ≤ ∑ j, η / ((freshEigenvalue H j - x) ^ 2 + η ^ 2) * X j :=
    hlow.trans hsingle
  have : X i ≤ 2 * η * ∑ j, η / ((freshEigenvalue H j - x) ^ 2 + η ^ 2) * X j := by
    rw [div_le_iff₀ (by positivity)] at key; linarith
  calc X i ≤ 2 * η * ∑ j, η / ((freshEigenvalue H j - x) ^ 2 + η ^ 2) * X j := this
    _ = 2 * N * η * ((N : ℝ)⁻¹ * ∑ j, η / ((freshEigenvalue H j - x) ^ 2 + η ^ 2) * X j) := by
        field_simp

/-!
## The bad events of the external local law along the flow
-/

/-- The isotropic bad event as a set of matrices `K = flowMatrix - F`. -/
def isoBadSet (F M : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) (z : ℂ) (thr : ℝ) :
    Set (Matrix (Fin N) (Fin N) ℂ) :=
  {K | thr < ‖star x ⬝ᵥ (((F + K - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - M) *ᵥ y)‖}

/-- The averaged bad event as a set of matrices. -/
def avgBadSet (F M B : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (thr : ℝ) :
    Set (Matrix (Fin N) (Fin N) ℂ) :=
  {K | thr < ‖CEH.normalizedTrace (((F + K - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - M) * B)‖}

theorem measurable_shiftInv (F : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) :
    Measurable (fun K : Matrix (Fin N) (Fin N) ℂ =>
      (F + K - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) := by
  refine measurable_matrix_inv.comp ?_
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.sub_apply, Matrix.add_apply]
  exact (measurable_const.add (measurable_matrixEntry i j)).sub measurable_const

theorem measurableSet_isoBadSet (F M : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) (z : ℂ)
    (thr : ℝ) : MeasurableSet (isoBadSet F M x y z thr) := by
  have h : Measurable (fun K : Matrix (Fin N) (Fin N) ℂ =>
      ‖star x ⬝ᵥ (((F + K - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - M) *ᵥ y)‖) := by
    refine Measurable.norm ?_
    simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply]
    refine Finset.measurable_sum _ fun a _ => measurable_const.mul
      (Finset.measurable_sum _ fun b _ => ?_)
    exact (((measurable_matrixEntry a b).comp (measurable_shiftInv F z)).sub measurable_const).mul
      measurable_const
  exact measurableSet_lt measurable_const h

theorem measurableSet_avgBadSet (F M B : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (thr : ℝ) :
    MeasurableSet (avgBadSet F M B z thr) := by
  have h : Measurable (fun K : Matrix (Fin N) (Fin N) ℂ =>
      ‖CEH.normalizedTrace (((F + K - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - M) * B)‖) := by
    refine Measurable.norm ?_
    simp only [CEH.normalizedTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sub_apply]
    refine measurable_const.mul (Finset.measurable_sum _ fun a _ => Finset.measurable_sum _
      fun b _ => ?_)
    exact (((measurable_matrixEntry a b).comp (measurable_shiftInv F z)).sub measurable_const).mul
      measurable_const
  exact measurableSet_lt measurable_const h

/-- The CEH isotropic bad event of `F + √σ W` is the flow's bad event at time `σ`. -/
theorem flowLaw_isotropicBad_eq {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a σ : ℝ}
    (ha : 0 ≤ a) (haσ : a ≤ σ) (M : CEH.MDEBranch (Real.sqrt σ) ⟨F, hF⟩) (x y : Fin N → ℂ)
    (z : ℂ) (δ : ℝ) :
    flowLaw N a {ω | (N : ℝ) ^ δ * CEH.isotropicControl (M.matrix z) z x y <
        ‖star x ⬝ᵥ (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
          M.matrix z) *ᵥ y)‖} =
      gueSourceLaw N (CEH.isotropicBadEvent M x y z δ) := by
  have h := flowLaw_preimage_eq_gueSourceLaw F ha haσ (measurableSet_isoBadSet F (M.matrix z) x y
    z ((N : ℝ) ^ δ * CEH.isotropicControl (M.matrix z) z x y))
  have e1 : {ω : FlowSample N | flowMatrix F a ω σ - F ∈ isoBadSet F (M.matrix z) x y z
      ((N : ℝ) ^ δ * CEH.isotropicControl (M.matrix z) z x y)} =
      {ω | (N : ℝ) ^ δ * CEH.isotropicControl (M.matrix z) z x y <
        ‖star x ⬝ᵥ (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
          M.matrix z) *ᵥ y)‖} := by
    ext ω; simp only [isoBadSet, Set.mem_ofPred_eq, add_sub_cancel]
  have e2 : {W : CEH.SourceHermitian N | ((Real.sqrt σ : ℝ) : ℂ) • W.1 ∈
      isoBadSet F (M.matrix z) x y z ((N : ℝ) ^ δ * CEH.isotropicControl (M.matrix z) z x y)} =
      CEH.isotropicBadEvent M x y z δ := by
    ext W; rfl
  rw [e1, e2] at h
  exact h

theorem flowLaw_averagedBad_eq {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a σ : ℝ}
    (ha : 0 ≤ a) (haσ : a ≤ σ) (M : CEH.MDEBranch (Real.sqrt σ) ⟨F, hF⟩)
    (B : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (δ : ℝ) :
    flowLaw N a {ω | (N : ℝ) ^ δ * CEH.averagedControl (M.matrix z) B z <
        ‖CEH.normalizedTrace (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
          M.matrix z) * B)‖} =
      gueSourceLaw N (CEH.averagedBadEvent M B z δ) := by
  have h := flowLaw_preimage_eq_gueSourceLaw F ha haσ (measurableSet_avgBadSet F (M.matrix z) B
    z ((N : ℝ) ^ δ * CEH.averagedControl (M.matrix z) B z))
  have e1 : {ω : FlowSample N | flowMatrix F a ω σ - F ∈ avgBadSet F (M.matrix z) B z
      ((N : ℝ) ^ δ * CEH.averagedControl (M.matrix z) B z)} =
      {ω | (N : ℝ) ^ δ * CEH.averagedControl (M.matrix z) B z <
        ‖CEH.normalizedTrace (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
          M.matrix z) * B)‖} := by
    ext ω; simp only [avgBadSet, Set.mem_ofPred_eq, add_sub_cancel]
  have e2 : {W : CEH.SourceHermitian N | ((Real.sqrt σ : ℝ) : ℂ) • W.1 ∈
      avgBadSet F (M.matrix z) B z ((N : ℝ) ^ δ * CEH.averagedControl (M.matrix z) B z)} =
      CEH.averagedBadEvent M B z δ := by
    ext W; rfl
  rw [e1, e2] at h
  exact h

/-- **Isotropic local law at one point** (from `ExternalLocalGUE`). -/
theorem flowLaw_isotropicBad_le (hELG : ExternalLocalGUE) (A C ε δ D : ℝ) (hε : 0 < ε)
    (hδ : 0 < δ) (hD : 0 < D) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (a σ : ℝ), 0 ≤ a → a ≤ σ → 0 < σ →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian),
        (Real.sqrt σ)⁻¹ * ‖F‖ ≤ C * (N : ℝ) ^ A →
        ∀ (M : CEH.MDEBranch (Real.sqrt σ) ⟨F, hF⟩) (z : ℂ), CEH.InLocalLawDomain M A ε z →
        ∀ x y : Fin N → ℂ,
          flowLaw N a {ω | (N : ℝ) ^ δ * CEH.isotropicControl (M.matrix z) z x y <
            ‖star x ⬝ᵥ (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
              M.matrix z) *ᵥ y)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  obtain ⟨N₀, hN₀, h⟩ := hELG A C ε δ D hε hδ hD
  refine ⟨N₀, hN₀, fun N hN a σ ha haσ hσ F hF hFn M z hz x y => ?_⟩
  rw [flowLaw_isotropicBad_eq hF ha haσ M x y z δ]
  exact (h N hN σ hσ ⟨F, hF⟩ hFn M z hz).1 x y

/-- **Averaged local law at one point** (from `ExternalLocalGUE`). -/
theorem flowLaw_averagedBad_le (hELG : ExternalLocalGUE) (A C ε δ D : ℝ) (hε : 0 < ε)
    (hδ : 0 < δ) (hD : 0 < D) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (a σ : ℝ), 0 ≤ a → a ≤ σ → 0 < σ →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian),
        (Real.sqrt σ)⁻¹ * ‖F‖ ≤ C * (N : ℝ) ^ A →
        ∀ (M : CEH.MDEBranch (Real.sqrt σ) ⟨F, hF⟩) (z : ℂ), CEH.InLocalLawDomain M A ε z →
        ∀ B : Matrix (Fin N) (Fin N) ℂ,
          flowLaw N a {ω | (N : ℝ) ^ δ * CEH.averagedControl (M.matrix z) B z <
            ‖CEH.normalizedTrace (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
              M.matrix z) * B)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  obtain ⟨N₀, hN₀, h⟩ := hELG A C ε δ D hε hδ hD
  refine ⟨N₀, hN₀, fun N hN a σ ha haσ hσ F hF hFn M z hz B => ?_⟩
  rw [flowLaw_averagedBad_eq hF ha haσ M B z δ]
  exact (h N hN σ hσ ⟨F, hF⟩ hFn M z hz).2 B

/-- With `MDEBranchIdentification`, the isotropic line in terms of CoareaPalm's `freshM`. -/
theorem flowLaw_isotropicBad_freshM_le (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification) (A C ε δ D : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hD : 0 < D) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (a σ : ℝ), 0 ≤ a → a ≤ σ → 0 < σ →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian),
        (Real.sqrt σ)⁻¹ * ‖F‖ ≤ C * (N : ℝ) ^ A →
        ∀ (M : CEH.MDEBranch (Real.sqrt σ) ⟨F, hF⟩) (z : ℂ), CEH.InLocalLawDomain M A ε z →
        0 < z.im → 0 < (freshDyson F σ z).im →
        ∀ x y : Fin N → ℂ,
          flowLaw N a {ω | (N : ℝ) ^ δ * CEH.isotropicControl (freshM F σ z) z x y <
            ‖star x ⬝ᵥ (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
              freshM F σ z) *ᵥ y)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  obtain ⟨N₀, hN₀, h⟩ := flowLaw_isotropicBad_le hELG A C ε δ D hε hδ hD
  refine ⟨N₀, hN₀, fun N hN a σ ha haσ hσ F hF hFn M z hz hzi hm x y => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le hN₀ hN
  have hMeq := mdeBranch_matrix_eq_freshM hMDE hNpos hF hσ hzi hm M
  have := h N hN a σ ha haσ hσ F hF hFn M z hz x y
  rwa [hMeq] at this

/-!
## The overlap bound on an energy grid
-/

/-- **Overlap bound at one time** (via `Im q*Gq`). For a finite grid `X` of energies at height
`η > 0` (each grid point in the local-law domain of the branch), outside an event of probability
`≤ |X| N^{-D}`, every eigenvalue within `η` of the grid has
`X_i(σ) ≤ 2Nη (Im q*M(x+iη)q + N^δ isotropicControl)`. -/
theorem overlap_bound_on_grid (hELG : ExternalLocalGUE) (A C ε δ D : ℝ) (hε : 0 < ε)
    (hδ : 0 < δ) (hD : 0 < D) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (a σ : ℝ), 0 ≤ a → a ≤ σ → 0 < σ →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian),
        (Real.sqrt σ)⁻¹ * ‖F‖ ≤ C * (N : ℝ) ^ A →
        ∀ (M : CEH.MDEBranch (Real.sqrt σ) ⟨F, hF⟩) (η : ℝ), 0 < η → ∀ (X : Finset ℝ),
        (∀ x ∈ X, CEH.InLocalLawDomain M A ε ⟨x, η⟩) → ∀ q : Fin N → ℂ,
          ∃ Bad : Set (FlowSample N), flowLaw N a Bad ≤ X.card * ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
            ∀ ω ∉ Bad, ω.1.IsHermitian → HasSimpleSpectrum N (flowMatrix F a ω σ) →
              ∀ (i : Fin N) (x : ℝ), x ∈ X → |flowEigenvalue F a ω σ i - x| ≤ η →
                flowOverlap F a q σ i ω ≤ 2 * N * η *
                  ((star q ⬝ᵥ (M.matrix ⟨x, η⟩ *ᵥ q)).im +
                    (N : ℝ) ^ δ * CEH.isotropicControl (M.matrix ⟨x, η⟩) ⟨x, η⟩ q q) := by
  obtain ⟨N₀, hN₀, h⟩ := flowLaw_isotropicBad_le hELG A C ε δ D hε hδ hD
  refine ⟨N₀, hN₀, fun N hN a σ ha haσ hσ F hF hFn M η hη X hX q => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le hN₀ hN
  set badx : ℝ → Set (FlowSample N) := fun x => {ω | (N : ℝ) ^ δ *
      CEH.isotropicControl (M.matrix ⟨x, η⟩) ⟨x, η⟩ q q <
      ‖star q ⬝ᵥ (((flowMatrix F a ω σ - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        M.matrix ⟨x, η⟩) *ᵥ q)‖}
  refine ⟨⋃ x ∈ X, badx x, ?_, ?_⟩
  · calc flowLaw N a (⋃ x ∈ X, badx x) ≤ ∑ x ∈ X, flowLaw N a (badx x) :=
          measure_biUnion_finset_le X badx
      _ ≤ ∑ _x ∈ X, ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
          Finset.sum_le_sum fun x hx => h N hN a σ ha haσ hσ F hF hFn M ⟨x, η⟩ (hX x hx) q q
      _ = X.card * ENNReal.ofReal ((N : ℝ) ^ (-D)) := by simp
  · intro ω hω hH hs i x hx hix
    have hnot : ω ∉ badx x := fun h' => hω (mem_biUnion hx h')
    simp only [badx, Set.mem_ofPred_eq, not_lt] at hnot
    have hHf := flowMatrix_isHermitian hF a hH σ
    have h1 := overlap_le_of_near hHf hs hNpos hη q i hix
    have h2 := im_quad_le ((flowMatrix F a ω σ - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)
      (M.matrix ⟨x, η⟩) q
    have hcoef : (0 : ℝ) ≤ 2 * N * η := by positivity
    calc flowOverlap F a q σ i ω
        ≤ 2 * N * η * (star q ⬝ᵥ ((flowMatrix F a ω σ -
            (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im := h1
      _ ≤ 2 * N * η * ((star q ⬝ᵥ (M.matrix ⟨x, η⟩ *ᵥ q)).im +
            (N : ℝ) ^ δ * CEH.isotropicControl (M.matrix ⟨x, η⟩) ⟨x, η⟩ q q) :=
          mul_le_mul_of_nonneg_left (h2.trans (by linarith [hnot])) hcoef

end BlockBand.Palm.MomentFlow
