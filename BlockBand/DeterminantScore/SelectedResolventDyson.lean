module

public import BlockBand.LocalWindow.ProofBranch

/-!
# Selected-energy Dyson regularity from the one-trace certificate

Deterministic stability results for the scalar Dyson equation:

* `dyson_two_point`: for two positive roots `m₁, m₂` of the scalar Dyson equation at `z₁, z₂`,
  `(m₁ - m₂)(1 - s T₁₂) = (z₁ - z₂) T₁₂`, `T₁₂ = ⟨r(z₁ + s m₁) r(z₂ + s m₂)⟩`.
* `dyson_lipschitz_local`: in the disc `‖z‖ ≤ δ_P`, `Im z ≥ 0`, of the uniform local plan
  `Palm.certificateLocalPlan` (where every root is within `ρ_P` of the reference `μ`), the secant
  coefficient stays at distance `≥ 3k/4` from `0` (Jacobian stability
  `Palm.certificate_jacobian_stable` plus `Palm.certificate_secant_variation`), so the root is
  `L`-Lipschitz in `z`, `L = 4/(3k) H⁻²`.
* `windowCenter_eq`: the exact identity `g(λ) = d⁻¹ Tr KΓ(λ) = λ + 2s Re m(λ)`,
  from `Tr X⁻¹(X⁻¹)* = d Im m / Im z` and `Im z = s Im m` at real `λ`.
* `pair_regular`: the package for the pair deformation `K` (reindexed to `Fin (2W)`): from
  `‖χ(K, c, 0, μ)‖ ≤ ε₁` with `V ≤ Im μ`, `‖μ‖ ≤ 1`: on the disc `‖z‖ ≤ δ`, `Im z ≥ 0`,
  `pairDyson K c z` is the positive root with `Im ≥ 3V/4`, `‖·‖ ≤ 2`, it is `L`-Lipschitz, and
  `‖m(0) - μ‖ ≤ L ‖χ‖`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedResolvent

open Matrix BlockBand.Palm
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate

section Scalar

variable {ι : Type*} [Fintype ι]

/-- The secant coefficient `T(a, b) = ⟨r(a) r(b)⟩`, `r(a) = (k - a)⁻¹`. -/
def secantAvg (spectrum : ι → ℝ) (a b : ℂ) : ℂ :=
  certificateAverage (fun i => certificateScalarResolvent (spectrum i) a *
    certificateScalarResolvent (spectrum i) b)

/-- **Two-point Dyson identity**: `(m₁ - m₂)(1 - s T₁₂) = (z₁ - z₂) T₁₂`. -/
theorem dyson_two_point (spectrum : ι → ℝ) (s : ℝ) {z₁ z₂ m₁ m₂ : ℂ}
    (h₁ : (z₁ + s * m₁).im ≠ 0) (h₂ : (z₂ + s * m₂).im ≠ 0)
    (hm₁ : certificateDysonResidual spectrum s z₁ m₁ = 0)
    (hm₂ : certificateDysonResidual spectrum s z₂ m₂ = 0) :
    (m₁ - m₂) * (1 - (s : ℂ) * secantAvg spectrum (z₁ + s * m₁) (z₂ + s * m₂)) =
      (z₁ - z₂) * secantAvg spectrum (z₁ + s * m₁) (z₂ + s * m₂) := by
  have e1 := (certificateDysonResidual_eq_zero_iff spectrum s z₁ m₁).mp hm₁
  have e2 := (certificateDysonResidual_eq_zero_iff spectrum s z₂ m₂).mp hm₂
  have hdiff : m₁ - m₂ = ((z₁ + s * m₁) - (z₂ + s * m₂)) *
      secantAvg spectrum (z₁ + s * m₁) (z₂ + s * m₂) := by
    refine (congrArg₂ (· - ·) e1 e2).trans ?_
    unfold certificateAverage secantAvg certificateAverage
    rw [← Finset.expect_sub_distrib, Finset.mul_expect]
    refine Finset.expect_congr rfl fun i _ => ?_
    rw [certificate_scalar_resolvent_sub _ h₁ h₂]
    ring
  linear_combination hdiff

variable [Nonempty ι]

theorem secantAvg_norm_le (spectrum : ι → ℝ) {H : ℝ} {a b : ℂ} (hH : 0 < H) (ha : H ≤ a.im)
    (hb : H ≤ b.im) : ‖secantAvg spectrum a b‖ ≤ H⁻¹ ^ 2 := by
  apply certificateAverage_norm_le_const
  intro i
  rw [norm_mul, sq]
  exact mul_le_mul (certificateScalarResolvent_norm_le _ hH ha)
    (certificateScalarResolvent_norm_le _ hH hb) (norm_nonneg _) (by positivity)

/-- The Lipschitz constant `4/(3k) H⁻²` of the local plan. -/
def dysonLip {c V : ℝ} (hc : 0 < c) (hV : 0 < V) : ℝ :=
  4 / (3 * (certificateLocalPlan hc hV).k) * (certificateLocalPlan hc hV).H⁻¹ ^ 2

theorem dysonLip_pos {c V : ℝ} (hc : 0 < c) (hV : 0 < V) : 0 < dysonLip hc hV := by
  have := (certificateLocalPlan hc hV).k_pos
  have := (certificateLocalPlan hc hV).H_pos
  unfold dysonLip; positivity

variable [DecidableEq ι]

/-- **Local Lipschitz bound for positive Dyson roots** (stability of the regularity certificate
in the local disc). -/
theorem dyson_lipschitz_local (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c V : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hV : 0 < V) {μ : ℂ} (hVμ : V ≤ μ.im)
    (hchi : ‖certificateChi F c 0 μ‖ ≤ (certificateLocalPlan hc hV).ε)
    {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im) (hz₂ : 0 ≤ z₂.im)
    (hz₁δ : ‖z₁‖ ≤ (certificateLocalPlan hc hV).δ) (hz₂δ : ‖z₂‖ ≤ (certificateLocalPlan hc hV).δ)
    (hm₁ : 3 * V / 4 ≤ m₁.im) (hm₂ : 3 * V / 4 ≤ m₂.im)
    (hr₁ : certificateDysonResidual hF.eigenvalues c z₁ m₁ = 0)
    (hr₂ : certificateDysonResidual hF.eigenvalues c z₂ m₂ = 0)
    (hρ₁ : ‖m₁ - μ‖ ≤ (certificateLocalPlan hc hV).ρ)
    (hρ₂ : ‖m₂ - μ‖ ≤ (certificateLocalPlan hc hV).ρ) :
    ‖m₁ - m₂‖ ≤ dysonLip hc hV * ‖z₁ - z₂‖ := by
  set P := certificateLocalPlan hc hV
  have hH := P.H_pos
  have hk := P.k_pos
  have hμ : 0 < μ.im := hV.trans_le hVμ
  -- Jacobian stability at the reference point
  have hsmallV : ‖certificateChi F c 0 μ‖ ≤ μ.im / 2 := by linarith [P.ε_V]
  have hsmallS : ‖certificateChi F c 0 μ‖ ≤ c * μ.im ^ 3 / 4 := by
    apply (hchi.trans P.ε_stable).trans
    gcongr
  have hJac := certificate_jacobian_stable F hF hc hμ hsmallV hsmallS
  have hJ : P.k ≤ ‖certificateDysonJacobian hF.eigenvalues c ((0 : ℝ) : ℂ) μ‖ := by
    apply le_trans _ ((Complex.re_le_norm _).trans' hJac)
    rw [P.k_eq]
    gcongr
  -- heights
  have hHc : P.H ≤ c * (3 * V / 4) := by rw [P.H_eq]; nlinarith
  have him : ∀ {z m : ℂ}, 0 ≤ z.im → 3 * V / 4 ≤ m.im → P.H ≤ (z + c * m).im := by
    intro z m hz hm
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero]
    nlinarith
  have ha₁ := him hz₁ hm₁
  have ha₂ := him hz₂ hm₂
  have ha₀ : P.H ≤ (((0 : ℝ) : ℂ) + c * μ).im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, zero_add]
    rw [P.H_eq]; nlinarith
  have hdist : ∀ {z m : ℂ}, ‖z‖ ≤ P.δ → ‖m - μ‖ ≤ P.ρ →
      ‖(z + c * m) - (((0 : ℝ) : ℂ) + c * μ)‖ ≤ P.δ + P.ρ := by
    intro z m hz hm
    have heq : (z + c * m) - (((0 : ℝ) : ℂ) + c * μ) = z + (c : ℂ) * (m - μ) := by
      push_cast; ring
    rw [heq]
    calc ‖z + (c : ℂ) * (m - μ)‖ ≤ ‖z‖ + c * ‖m - μ‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      _ ≤ P.δ + 1 * P.ρ := by gcongr
      _ = P.δ + P.ρ := by ring
  have hsec := certificate_secant_variation hF.eigenvalues (s := c) hH hc.le ha₁ ha₂ ha₀
    (hdist hz₁δ hρ₁) (hdist hz₂δ hρ₂)
  rw [sub_self, abs_zero, zero_mul, zero_add] at hsec
  have hδS : 2 * c * P.δ * P.H⁻¹ ^ 3 ≤ P.k / 8 := by
    calc
      _ ≤ 2 * c * (P.k * P.H ^ 3 / (16 * c)) * P.H⁻¹ ^ 3 := by gcongr; exact P.δ_stable
      _ = _ := by field_simp [P.H_pos.ne', hc.ne']; ring
  have hρS : 2 * c * P.ρ * P.H⁻¹ ^ 3 ≤ P.k / 8 := by
    calc
      _ ≤ 2 * c * (P.k * P.H ^ 3 / (16 * c)) * P.H⁻¹ ^ 3 := by gcongr; exact P.ρ_stable
      _ = _ := by field_simp [P.H_pos.ne', hc.ne']; ring
  have hsec' : 2 * c * (P.δ + P.ρ) * P.H⁻¹ ^ 3 ≤ P.k / 4 := by nlinarith
  set T := secantAvg hF.eigenvalues (z₁ + c * m₁) (z₂ + c * m₂)
  have hJT : ‖1 - (c : ℂ) * T‖ ≥ 3 * P.k / 4 := by
    have hJdef : certificateDysonJacobian hF.eigenvalues c ((0 : ℝ) : ℂ) μ =
        (1 - (c : ℂ) * T) + ((c : ℂ) * T - (c : ℂ) * certificateAverage (fun i =>
          certificateScalarResolvent (hF.eigenvalues i) (((0 : ℝ) : ℂ) + c * μ) ^ 2)) := by
      unfold certificateDysonJacobian; ring
    have h1 := norm_add_le (1 - (c : ℂ) * T) ((c : ℂ) * T - (c : ℂ) * certificateAverage
      (fun i => certificateScalarResolvent (hF.eigenvalues i) (((0 : ℝ) : ℂ) + c * μ) ^ 2))
    rw [← hJdef] at h1
    have h2 : ‖(c : ℂ) * T - (c : ℂ) * certificateAverage (fun i =>
        certificateScalarResolvent (hF.eigenvalues i) (((0 : ℝ) : ℂ) + c * μ) ^ 2)‖ ≤
        P.k / 4 := hsec.trans hsec'
    linarith
  have hT : ‖T‖ ≤ P.H⁻¹ ^ 2 := secantAvg_norm_le _ hH ha₁ ha₂
  have hid := dyson_two_point hF.eigenvalues c (hH.trans_le ha₁).ne' (hH.trans_le ha₂).ne' hr₁ hr₂
  have hnorm := congrArg norm hid
  rw [norm_mul, norm_mul] at hnorm
  have hm0 : 0 ≤ ‖m₁ - m₂‖ := norm_nonneg _
  have hmain : ‖m₁ - m₂‖ * (3 * P.k / 4) ≤ ‖z₁ - z₂‖ * P.H⁻¹ ^ 2 := by
    calc ‖m₁ - m₂‖ * (3 * P.k / 4) ≤ ‖m₁ - m₂‖ * ‖1 - (c : ℂ) * T‖ :=
          mul_le_mul_of_nonneg_left hJT hm0
      _ = ‖z₁ - z₂‖ * ‖T‖ := hnorm
      _ ≤ ‖z₁ - z₂‖ * P.H⁻¹ ^ 2 := mul_le_mul_of_nonneg_left hT (norm_nonneg _)
  have hk3 : 0 < 3 * P.k / 4 := by positivity
  show ‖m₁ - m₂‖ ≤ 4 / (3 * P.k) * P.H⁻¹ ^ 2 * ‖z₁ - z₂‖
  have : ‖m₁ - m₂‖ ≤ ‖z₁ - z₂‖ * P.H⁻¹ ^ 2 / (3 * P.k / 4) := by
    rw [le_div_iff₀ hk3]; exact hmain
  refine this.trans (le_of_eq ?_)
  field_simp

/-- **Roots on the local disc**: under the plan certificate bound, for `Im z ≥ 0`, `‖z‖ ≤ δ_P`,
the canonical root exists, has `Im ≥ 3V/4` and is within `ρ_P` of `μ`. -/
theorem canonical_local (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c V : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hV : 0 < V) {μ : ℂ} (hVμ : V ≤ μ.im)
    (hchi : ‖certificateChi F c 0 μ‖ ≤ (certificateLocalPlan hc hV).ε)
    {z : ℂ} (hz : 0 ≤ z.im) (hzδ : ‖z‖ ≤ (certificateLocalPlan hc hV).δ) :
    3 * V / 4 ≤ (certificateCanonicalDyson hF.eigenvalues c z).im ∧
      certificateDysonResidual hF.eigenvalues c z (certificateCanonicalDyson hF.eigenvalues c z)
        = 0 ∧
      ‖certificateCanonicalDyson hF.eigenvalues c z - μ‖ ≤ (certificateLocalPlan hc hV).ρ := by
  set P := certificateLocalPlan hc hV
  have hshift : ‖z + c * μ - (((0 : ℝ) : ℂ) + c * μ)‖ ≤ P.δ := by
    simpa using hzδ
  have hsc : |c - c| ≤ P.δ := by rw [sub_self, abs_zero]; exact P.δ_pos.le
  obtain ⟨m, him, hmzero, hmρ, -⟩ :=
    certificate_uniform_local_zero F hF hc hV hVμ P hchi hc.le hc1.le hshift hsc
  have hmpos : 0 < m.im := lt_of_lt_of_le (by positivity) him
  rw [certificateCanonicalDyson_eq hF.eigenvalues hc hz hmpos hmzero]
  exact ⟨him, hmzero, hmρ⟩

end Scalar

/-!
## `freshDyson` is the canonical root
-/

section Fresh

variable {N : ℕ}

theorem trace_inv_eq_certificateMatrixTrace (F : Matrix (Fin N) (Fin N) ℂ) (w : ℂ) :
    (N : ℂ)⁻¹ * (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹.trace =
      certificateMatrixTrace F w := by
  unfold certificateMatrixTrace certificateMatrixResolvent
  rw [Fintype.card_fin, div_eq_inv_mul]

/-- **`freshDyson` = the positive root** (uniqueness at `Im z ≥ 0`). -/
theorem freshDyson_eq_of_residual [NeZero N] (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian)
    {s : ℝ} (hs : 0 < s) {z m : ℂ} (hz : 0 ≤ z.im) (hm : 0 < m.im)
    (hr : certificateDysonResidual hF.eigenvalues s z m = 0) : freshDyson F s z = m := by
  have key : ∀ m' : ℂ, 0 < m'.im →
      (m' = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * m') • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹.trace ↔
        certificateDysonResidual hF.eigenvalues s z m' = 0) := by
    intro m' hm'
    have hw : (z + (s : ℂ) * m').im ≠ 0 := by
      have : 0 < (z + (s : ℂ) * m').im := by
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero]
        positivity
      exact this.ne'
    rw [trace_inv_eq_certificateMatrixTrace, certificateMatrixTrace_eq_average F hF hw,
      certificateDysonResidual_eq_zero_iff]
  unfold freshDyson
  split_ifs with h
  · obtain ⟨hpos, hspec⟩ := Classical.choose_spec h
    exact certificate_dyson_unique_nonnegative hF.eigenvalues hs hz hpos hm
      ((key _ hpos).1 hspec) hr
  · exact absurd ⟨m, hm, (key m hm).2 hr⟩ h

end Fresh

/-!
## The window centre identity
-/

section Center

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `Tr K (X*X)⁻¹ = conj (Tr X⁻¹) + z Tr (X*X)⁻¹` and `(z - z̄) Tr (X*X)⁻¹ = Tr X⁻¹ - conj Tr X⁻¹`
for `X = K - z`, `K` Hermitian, `Im z ≠ 0`. -/
theorem trace_gamma_identities {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (K * ((K - z • 1)ᴴ * (K - z • 1))⁻¹).trace =
        star ((K - z • 1)⁻¹.trace) + z * (((K - z • 1)ᴴ * (K - z • 1))⁻¹).trace ∧
      (z - star z) * (((K - z • 1)ᴴ * (K - z • 1))⁻¹).trace =
        (K - z • 1)⁻¹.trace - star ((K - z • 1)⁻¹.trace) := by
  set X := K - z • (1 : Matrix ι ι ℂ)
  have hz' : (star z).im ≠ 0 := by rw [Complex.star_def, Complex.conj_im]; exact neg_ne_zero.mpr hz
  have hX : IsUnit X.det := isUnit_iff_ne_zero.mpr
    (BlockBand.LocalWindow.ProofCertificate.det_sub_smul_ne_zero hK hz)
  have hXH : Xᴴ = K - star z • (1 : Matrix ι ι ℂ) := by
    simp only [X, conjTranspose_sub, hK.eq, conjTranspose_smul, conjTranspose_one]
  have hXHu : IsUnit Xᴴ.det := by
    rw [hXH]; exact isUnit_iff_ne_zero.mpr
      (BlockBand.LocalWindow.ProofCertificate.det_sub_smul_ne_zero hK hz')
  have hinv : (Xᴴ * X)⁻¹ = X⁻¹ * Xᴴ⁻¹ := Matrix.mul_inv_rev _ _
  have hKX : K = X + z • (1 : Matrix ι ι ℂ) := by simp [X]
  have hXHinv : Xᴴ⁻¹ = X⁻¹ᴴ := (conjTranspose_nonsing_inv X).symm
  constructor
  · rw [hinv]
    conv_lhs => rw [hKX]
    rw [Matrix.add_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.one_mul,
      trace_add, Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul, hXHinv,
      trace_conjTranspose]
  · rw [hinv]
    have h1 : X⁻¹ - Xᴴ⁻¹ = X⁻¹ * (Xᴴ - X) * Xᴴ⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXHu,
        Matrix.mul_one, Matrix.nonsing_inv_mul _ hX, Matrix.one_mul]
    have h2 : Xᴴ - X = (z - star z) • (1 : Matrix ι ι ℂ) := by
      rw [hXH]; simp only [X, sub_smul]; abel
    rw [h2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h1
    have h3 := congrArg Matrix.trace h1
    rw [trace_sub, trace_smul, smul_eq_mul, hXHinv, trace_conjTranspose] at h3
    rw [hXHinv]
    exact h3.symm

end Center

/-!
## The pair deformation
-/

section Pair

open BlockBand.Model.Construction BlockBand.Internal.Contracts.Layers BlockBand.LocalWindow

variable {p : Parameters} {i : ZMod p.n}

theorem card_pairSite_complex : (Fintype.card (PairSite p i) : ℂ) = 2 * (p.W : ℂ) := by
  rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring

/-- **The window centre identity**: if `m = pairDyson K s λ` is a positive root,
`m = ⟨(K - λ - s m)⁻¹⟩`, then `g(λ) = d⁻¹ Tr KΓ(λ) = λ + 2s Re m`. -/
theorem windowCenter_eq {K : PairMatrix p i} (hK : K.IsHermitian) {s lam : ℝ} (hs : 0 < s)
    (hm : 0 < (pairDyson p i K s lam).im)
    (heq : pairDyson p i K s lam =
      certificateMatrixTrace K ((lam : ℂ) + s * pairDyson p i K s lam)) :
    windowCenter p i K K s lam = lam + 2 * s * (pairDyson p i K s lam).re := by
  set m := pairDyson p i K s lam with hmdef
  set z : ℂ := (lam : ℂ) + s * m with hzdef
  have hzim : z.im = s * m.im := by simp [z, Complex.mul_im]
  have hz : z.im ≠ 0 := by rw [hzim]; positivity
  obtain ⟨h1, h2⟩ := trace_gamma_identities hK hz
  set Q := (((K - z • 1)ᴴ * (K - z • 1))⁻¹).trace
  set T := (K - z • (1 : PairMatrix p i))⁻¹.trace
  have hW : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  have hWr : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hT : T = 2 * (p.W : ℂ) * m := by
    have h := heq
    unfold certificateMatrixTrace certificateMatrixResolvent at h
    rw [card_pairSite_complex] at h
    rw [h]; field_simp; rfl
  have hzz : z - star z = ((2 * s * m.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [z, Complex.mul_im, Complex.mul_re]
    ring
  have hTT : T - star T = ((2 * (2 * p.W) * m.im : ℝ) : ℂ) * Complex.I := by
    rw [hT]; apply Complex.ext <;> simp [Complex.mul_im, Complex.mul_re]
    ring
  have hQ : Q = ((2 * p.W / s : ℝ) : ℂ) := by
    have hne : ((2 * s * m.im : ℝ) : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (by positivity : (2 * s * m.im) ≠ 0)) Complex.I_ne_zero
    apply mul_left_cancel₀ hne
    calc ((2 * s * m.im : ℝ) : ℂ) * Complex.I * Q = (z - star z) * Q := by rw [hzz]
      _ = T - star T := h2
      _ = _ := by
        rw [hTT]; push_cast
        have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
        field_simp
  unfold windowCenter windowGamma
  simp only []
  rw [← hmdef, ← hzdef, Matrix.mul_smul, trace_smul, smul_eq_mul, h1, hT, hQ]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, star_mul', Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.mul_im, z,
    Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re, Complex.natCast_im, map_ofNat,
    map_natCast]
  field_simp
  ring

/-- **The regularity package for the pair deformation** (the regularity certificate
lemma). Fixed `0 < c < 1`, `V > 0`; then `ε₁, δ, L > 0`; for every pair
and Hermitian `K` and every reference `μ` with `V ≤ Im μ`, `‖μ‖ ≤ 1`,
`‖χ‖ = ‖⟨(K - cμ)⁻¹⟩ - μ‖ ≤ ε₁`: on the disc `‖z‖ ≤ δ`, `Im z ≥ 0`, `m = pairDyson K c z` is a
root, `m = ⟨(K - z - cm)⁻¹⟩`, with `Im m ≥ 3V/4` and `‖m‖ ≤ 2`; `m` is `L`-Lipschitz there; and
`‖m(0) - μ‖ ≤ L ‖χ‖`. -/
theorem pair_regular {c V : ℝ} (hc : 0 < c) (hc1 : c < 1) (hV : 0 < V) :
    ∃ ε₁ δ L : ℝ, 0 < ε₁ ∧ 0 < δ ∧ 0 < L ∧
      ∀ (p : Parameters) (i : ZMod p.n) (K : PairMatrix p i), K.IsHermitian →
        ∀ μ : ℂ, V ≤ μ.im → ‖μ‖ ≤ 1 → ‖certificateChi K c 0 μ‖ ≤ ε₁ →
          (∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ δ →
            3 * V / 4 ≤ (pairDyson p i K c z).im ∧ ‖pairDyson p i K c z‖ ≤ 2 ∧
              pairDyson p i K c z = certificateMatrixTrace K (z + c * pairDyson p i K c z)) ∧
          (∀ z₁ z₂ : ℂ, 0 ≤ z₁.im → 0 ≤ z₂.im → ‖z₁‖ ≤ δ → ‖z₂‖ ≤ δ →
            ‖pairDyson p i K c z₁ - pairDyson p i K c z₂‖ ≤ L * ‖z₁ - z₂‖) ∧
          ‖pairDyson p i K c 0 - μ‖ ≤ L * ‖certificateChi K c 0 μ‖ := by
  set P := certificateLocalPlan hc hV
  refine ⟨P.ε, P.δ, max (dysonLip hc hV) (8 / (c * V ^ 2)), P.ε_pos, P.δ_pos,
    lt_max_of_lt_left (dysonLip_pos hc hV), ?_⟩
  intro p i K hK μ hVμ hμ1 hchiK
  set e := Fintype.equivFin (PairSite p i)
  set F := reindex e e K with hFdef
  have hF : F.IsHermitian := hK.reindex e
  have : NeZero (Fintype.card (PairSite p i)) := ⟨by
    rw [BlockBand.Angular.FiberAngular.card_pairSite]; have := p.W_pos; omega⟩
  have hchiF : certificateChi F c 0 μ = certificateChi K c 0 μ := by
    unfold certificateChi
    rw [BlockBand.LocalWindow.ProofCertificate.certificateMatrixTrace_reindex]
  have hchi : ‖certificateChi F c 0 μ‖ ≤ P.ε := hchiF ▸ hchiK
  have hpd : ∀ z : ℂ, pairDyson p i K c z = freshDyson F c z := fun z => rfl
  have hloc : ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ P.δ →
      pairDyson p i K c z = certificateCanonicalDyson hF.eigenvalues c z ∧
      3 * V / 4 ≤ (certificateCanonicalDyson hF.eigenvalues c z).im ∧
      certificateDysonResidual hF.eigenvalues c z (certificateCanonicalDyson hF.eigenvalues c z)
        = 0 ∧
      ‖certificateCanonicalDyson hF.eigenvalues c z - μ‖ ≤ P.ρ := by
    intro z hz hzδ
    obtain ⟨him, hres, hρ⟩ := canonical_local F hF hc hc1 hV hVμ hchi hz hzδ
    refine ⟨?_, him, hres, hρ⟩
    rw [hpd]
    exact freshDyson_eq_of_residual F hF hc hz (lt_of_lt_of_le (by positivity) him) hres
  refine ⟨fun z hz hzδ => ?_, fun z₁ z₂ hz₁ hz₂ hz₁δ hz₂δ => ?_, ?_⟩
  · obtain ⟨heq, him, hres, hρ⟩ := hloc z hz hzδ
    rw [heq]
    refine ⟨him, ?_, ?_⟩
    · have hρV := P.ρ_V
      have hVle : V ≤ 1 := hVμ.trans ((Complex.im_le_norm μ).trans hμ1)
      calc ‖certificateCanonicalDyson hF.eigenvalues c z‖
          ≤ ‖certificateCanonicalDyson hF.eigenvalues c z - μ‖ + ‖μ‖ := norm_le_norm_sub_add _ _
        _ ≤ 2 := by linarith
    · have hpos : 0 < (certificateCanonicalDyson hF.eigenvalues c z).im :=
        lt_of_lt_of_le (by positivity) him
      have hw : (z + (c : ℂ) * certificateCanonicalDyson hF.eigenvalues c z).im ≠ 0 := by
        have : 0 < (z + (c : ℂ) * certificateCanonicalDyson hF.eigenvalues c z).im := by
          simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, add_zero]
          positivity
        exact this.ne'
      have h := (certificateDysonResidual_eq_zero_iff _ _ _ _).mp hres
      rw [← BlockBand.LocalWindow.ProofCertificate.certificateMatrixTrace_reindex e,
        certificateMatrixTrace_eq_average F hF hw]
      exact h
  · obtain ⟨heq₁, him₁, hres₁, hρ₁⟩ := hloc z₁ hz₁ hz₁δ
    obtain ⟨heq₂, him₂, hres₂, hρ₂⟩ := hloc z₂ hz₂ hz₂δ
    rw [heq₁, heq₂]
    exact (dyson_lipschitz_local F hF hc hc1 hV hVμ hchi hz₁ hz₂ hz₁δ hz₂δ him₁ him₂ hres₁ hres₂
      hρ₁ hρ₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · have hchi' : ‖certificateChi F c 0 μ‖ ≤ (certificateLocalPlan hc hV).ε := hchi
    obtain ⟨m, him, hres, -, hdist⟩ :=
      certificate_chi_only_reference_zero F hF hc hc1 hV hVμ hchi'
    have hpos : 0 < m.im := lt_of_lt_of_le (by positivity) him
    have h0 : pairDyson p i K c 0 = m := by
      rw [hpd]
      have := freshDyson_eq_of_residual F hF hc (z := ((0 : ℝ) : ℂ)) (by simp) hpos hres
      simpa using this
    rw [h0, ← hchiF]
    exact hdist.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end Pair

end BlockBand.DeterminantScore.SelectedResolvent
