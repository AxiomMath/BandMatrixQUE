module

public import BlockBand.LocalWindow.ProofETHCenter

/-!
# The regular window of the external ETH theorem from a root rectangle

Lipschitz and differentiability properties of the Dyson root on a root rectangle, which give the
regular-window hypothesis of the external ETH theorem in part (ii) of the physical local-window
lemma.

Setting: Hermitian `F` on `Fin N` (`N > 0`), `s > 0`. `RootRectangle F s E₀ r v₀`: at every
`x + iη` with `|x - E₀| ≤ r`, `0 ≤ η ≤ 1`, a Dyson root `m` (`IsDysonRoot`) with `Im m ≥ v₀`
exists. The real-axis root is `realRoot F s x = freshDyson F s x` and
`realResolvent F s x = (F - x - s m(x))⁻¹`.

## Main results

* `root_lipschitz`, `resolvent_lipschitz`: `|m₁ - m₂| ≤ L |z₁ - z₂|`,
  `‖M₁ - M₂‖ ≤ L' |z₁ - z₂|` with `L = (2s²v₀²)⁻¹`, `L' = (1 + sL)(sv₀)⁻²` (operator norm).
* `hasDerivAt_realRoot`: `m'(E) = t/(N - s t)`, `t = Tr M(E)²`, inside the window;
  `hasDerivAt_realResolvent`: `M'(E) = (1 + s m'(E)) M(E)²`.
* `regularWindow_of_rootRectangle`: under `Inputs.MDEBranchIdentification`, every branch
  `M` of `F` at `λ = √s` satisfies `Inputs.RegularWindow M E₀ r K` for every
  `K ≥ regK s v₀ = max(L', (sv₀)⁻¹, v₀⁻¹, (2sv₀²)⁻¹)`, with boundary values `realResolvent`.
  `regK` depends only on `s` and `v₀` (not on `N`, `F` or `E₀`), and is antitone in `s`
  (`regK_anti`), so it is uniform over a compact range of variances.
* `rootRectangle_of_poleCertificate`: the certificate
  (`ProofCertificate.poleCertificate_regular`) gives, for every `s' ∈ [s - s₀, s]`, the root
  rectangle of the truncated deformation `F̂(e)` around `e`; `rootRectangle_reindex` moves it to
  `Fin N`, `isDysonRoot_sub_smul` shifts the spectral parameter (`F̂(e) - c` at `z` is `F̂(e)` at
  `z + c`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofETH

open Matrix Filter Topology Set
open BlockBand.External BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate Matrix.Norms.L2Operator

/-!
## Operator-norm bounds
-/

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `‖A‖ ≤ c` (`L²` operator norm) from `‖A v‖² ≤ c² ‖v‖²`. -/
theorem opNorm_le_of_sqNorm {A : Matrix ι ι ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : ι → ℂ, sqNorm (A *ᵥ v) ≤ c ^ 2 * sqNorm v) : ‖A‖ ≤ c := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have e1 : ∀ v : ι → ℂ, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ = Real.sqrt (sqNorm v) := by
    intro v; rw [EuclideanSpace.norm_eq]; rfl
  have key : Real.sqrt (sqNorm (A *ᵥ WithLp.ofLp x)) ≤ c * Real.sqrt (sqNorm (WithLp.ofLp x)) := by
    calc Real.sqrt (sqNorm (A *ᵥ WithLp.ofLp x))
        ≤ Real.sqrt (c ^ 2 * sqNorm (WithLp.ofLp x)) := Real.sqrt_le_sqrt (h _)
      _ = c * Real.sqrt (sqNorm (WithLp.ofLp x)) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  rw [← e1, ← e1, WithLp.toLp_ofLp] at key
  exact key

/-- `‖(F - w)⁻¹‖ ≤ |Im w|⁻¹` for Hermitian `F`. -/
theorem opNorm_resolvent_le {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {w : ℂ} (hw : w.im ≠ 0) :
    ‖(F - w • (1 : Matrix ι ι ℂ))⁻¹‖ ≤ |w.im|⁻¹ :=
  opNorm_le_of_sqNorm (inv_nonneg.mpr (abs_nonneg _)) (sqNorm_resolvent_le hF hw)

/-- The difference identity of two Dyson roots:
`(m₁ - m₂)(N - s Tr M₁M₂) = (z₁ - z₂) Tr M₁M₂`. -/
theorem dyson_diff_identity [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im) (hz₂ : 0 ≤ z₂.im)
    (h₁ : IsDysonRoot F s z₁ m₁) (h₂ : IsDysonRoot F s z₂ m₂) :
    (m₁ - m₂) * ((Fintype.card ι : ℂ) - s * ((F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace) =
      (z₁ - z₂) * ((F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace := by
  have hw₁ := (dysonRoot_w_im_pos hs hz₁ h₁.1).ne'
  have hw₂ := (dysonRoot_w_im_pos hs hz₂ h₂.1).ne'
  have hNne : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have e := congrArg Matrix.trace (resolvent_sub hF hw₁ hw₂)
  rw [trace_sub, trace_smul, smul_eq_mul] at e
  have e1 : ((F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹).trace =
      (Fintype.card ι : ℂ) * m₁ := by
    conv_rhs => rw [h₁.2]
    rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
  have e2 : ((F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace =
      (Fintype.card ι : ℂ) * m₂ := by
    conv_rhs => rw [h₂.2]
    rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
  rw [e1, e2] at e
  linear_combination e

/-- `2 s N v₀² ≤ |N - s Tr M₁M₂|` for two roots with `Im m_j ≥ v₀ ≥ 0`. -/
theorem stability_lower [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im) (hz₂ : 0 ≤ z₂.im)
    (h₁ : IsDysonRoot F s z₁ m₁) (h₂ : IsDysonRoot F s z₂ m₂) {v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    (hv₁ : v₀ ≤ m₁.im) (hv₂ : v₀ ≤ m₂.im) :
    2 * s * Fintype.card ι * v₀ ^ 2 ≤
      ‖(Fintype.card ι : ℂ) - s * ((F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace‖ := by
  have hstab := dyson_stability hF hs hz₁ hz₂ h₁ h₂
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hsq : 4 * v₀ ^ 2 ≤ (m₁.im + m₂.im) ^ 2 := by nlinarith
  have hre : ((Fintype.card ι : ℂ) - s * ((F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace).re =
      Fintype.card ι - s * ((F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace.re := by
    simp [Complex.mul_re]
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [hre]
  have : 2 * s * Fintype.card ι * v₀ ^ 2 ≤ s / 2 * Fintype.card ι * (m₁.im + m₂.im) ^ 2 := by
    have h1 : 0 ≤ s / 2 * Fintype.card ι := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsq h1]
  linarith

/-- The Lipschitz constant of the root, `L = (2s²v₀²)⁻¹`. -/
def rootLip (s v₀ : ℝ) : ℝ := (2 * s ^ 2 * v₀ ^ 2)⁻¹

/-- The Lipschitz constant of the root resolvent, `L' = (1 + sL)(sv₀)⁻²`. -/
def resLip (s v₀ : ℝ) : ℝ := (1 + s * rootLip s v₀) * ((s * v₀)⁻¹) ^ 2

/-- The constant of `RegularWindow`: `max(L', (sv₀)⁻¹, v₀⁻¹, (2sv₀²)⁻¹)`. -/
def regK (s v₀ : ℝ) : ℝ := max (max (resLip s v₀) (s * v₀)⁻¹) (max v₀⁻¹ (2 * s * v₀ ^ 2)⁻¹)

theorem rootLip_nonneg (s v₀ : ℝ) : 0 ≤ rootLip s v₀ := by unfold rootLip; positivity

/-- **Lipschitz bound of the root**: `|m₁ - m₂| ≤ L |z₁ - z₂|` for roots with `Im m_j ≥ v₀ > 0`. -/
theorem root_lipschitz [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im) (hz₂ : 0 ≤ z₂.im)
    (h₁ : IsDysonRoot F s z₁ m₁) (h₂ : IsDysonRoot F s z₂ m₂) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hv₁ : v₀ ≤ m₁.im) (hv₂ : v₀ ≤ m₂.im) :
    ‖m₁ - m₂‖ ≤ rootLip s v₀ * ‖z₁ - z₂‖ := by
  have h := dyson_lipschitz hF hs hz₁ hz₂ h₁ h₂
  have hsq : 4 * v₀ ^ 2 ≤ (m₁.im + m₂.im) ^ 2 := by nlinarith
  have hpos : 0 < 2 * s ^ 2 * v₀ ^ 2 := by positivity
  have h2 : ‖m₁ - m₂‖ * (2 * s ^ 2 * v₀ ^ 2) ≤ ‖z₁ - z₂‖ := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) h
    have : 0 ≤ s ^ 2 / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsq this]
  unfold rootLip
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  exact h2

/-- `‖(F - w)⁻¹‖ ≤ (s v₀)⁻¹` at a root with `Im m ≥ v₀ > 0` (`w = z + s m`, `Im z ≥ 0`). -/
theorem opNorm_root_resolvent_le {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {z m : ℂ} (hz : 0 ≤ z.im) {v₀ : ℝ} (hv₀ : 0 < v₀) (hv : v₀ ≤ m.im) :
    ‖(F - (z + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹‖ ≤ (s * v₀)⁻¹ := by
  have hm : 0 < m.im := hv₀.trans_le hv
  have hw := dysonRoot_w_im_pos hs hz hm
  refine (opNorm_resolvent_le hF hw.ne').trans ?_
  rw [abs_of_pos hw]
  refine inv_anti₀ (mul_pos hs hv₀) ?_
  have := dysonRoot_w_im (s := s) (m := m) hz
  nlinarith

/-- **Lipschitz bound of the root resolvent**: `‖M₁ - M₂‖ ≤ L' |z₁ - z₂|`. -/
theorem resolvent_lipschitz [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im) (hz₂ : 0 ≤ z₂.im)
    (h₁ : IsDysonRoot F s z₁ m₁) (h₂ : IsDysonRoot F s z₂ m₂) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hv₁ : v₀ ≤ m₁.im) (hv₂ : v₀ ≤ m₂.im) :
    ‖(F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ -
        (F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹‖ ≤ resLip s v₀ * ‖z₁ - z₂‖ := by
  have hw₁ := (dysonRoot_w_im_pos hs hz₁ h₁.1).ne'
  have hw₂ := (dysonRoot_w_im_pos hs hz₂ h₂.1).ne'
  rw [resolvent_sub hF hw₁ hw₂, norm_smul]
  have hM₁ := opNorm_root_resolvent_le hF hs hz₁ hv₀ hv₁
  have hM₂ := opNorm_root_resolvent_le hF hs hz₂ hv₀ hv₂
  have hprod : ‖(F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
      (F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹‖ ≤ ((s * v₀)⁻¹) ^ 2 := by
    refine (norm_mul_le _ _).trans ?_
    rw [sq]
    exact mul_le_mul hM₁ hM₂ (norm_nonneg _) (inv_nonneg.mpr (mul_pos hs hv₀).le)
  have hm := root_lipschitz hF hs hz₁ hz₂ h₁ h₂ hv₀ hv₁ hv₂
  have hw : ‖(z₁ + (s : ℂ) * m₁) - (z₂ + (s : ℂ) * m₂)‖ ≤ (1 + s * rootLip s v₀) * ‖z₁ - z₂‖ := by
    have e : (z₁ + (s : ℂ) * m₁) - (z₂ + (s : ℂ) * m₂) = (z₁ - z₂) + (s : ℂ) * (m₁ - m₂) := by
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    nlinarith [mul_le_mul_of_nonneg_left hm hs.le]
  unfold resLip
  calc ‖(z₁ + (s : ℂ) * m₁) - (z₂ + (s : ℂ) * m₂)‖ *
        ‖(F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
          (F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹‖
      ≤ ((1 + s * rootLip s v₀) * ‖z₁ - z₂‖) * ((s * v₀)⁻¹) ^ 2 :=
        mul_le_mul hw hprod (norm_nonneg _) (by
          have := rootLip_nonneg s v₀; positivity)
    _ = (1 + s * rootLip s v₀) * ((s * v₀)⁻¹) ^ 2 * ‖z₁ - z₂‖ := by ring

end Generic

/-!
## The real axis
-/

section RealLine

variable {N : ℕ} [NeZero N]

/-- The real-axis Dyson root `m(x) = freshDyson F s x` (`m_s(x)` of the fresh regularity estimate). -/
def realRoot (F : Matrix (Fin N) (Fin N) ℂ) (s x : ℝ) : ℂ :=
  BlockBand.Internal.Contracts.CoareaPalm.freshDyson F s (x : ℂ)

/-- The real-axis root resolvent `M(x) = (F - x - s m(x))⁻¹` (the boundary value `M_s(x)`). -/
def realResolvent (F : Matrix (Fin N) (Fin N) ℂ) (s x : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  (F - ((x : ℂ) + (s : ℂ) * realRoot F s x) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- The root rectangle (the conclusion of `ProofCertificate.poleCertificate_regular`, lower bound):
at every `x + iη`, `|x - E₀| ≤ r`, `0 ≤ η ≤ 1`, a Dyson root with `Im m ≥ v₀` exists. -/
def RootRectangle (F : Matrix (Fin N) (Fin N) ℂ) (s E₀ r v₀ : ℝ) : Prop :=
  ∀ x : ℝ, |x - E₀| ≤ r → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
    ∃ m : ℂ, IsDysonRoot F s ((x : ℂ) + (η : ℂ) * Complex.I) m ∧ v₀ ≤ m.im

variable {F : Matrix (Fin N) (Fin N) ℂ} {s E₀ r v₀ : ℝ}

theorem realRoot_spec (hF : F.IsHermitian) (hs : 0 < s) (hR : RootRectangle F s E₀ r v₀)
    {x : ℝ} (hx : |x - E₀| ≤ r) :
    IsDysonRoot F s (x : ℂ) (realRoot F s x) ∧ v₀ ≤ (realRoot F s x).im := by
  obtain ⟨m, hm, hv⟩ := hR x hx 0 le_rfl zero_le_one
  rw [Complex.ofReal_zero, zero_mul, add_zero] at hm
  have e : realRoot F s x = m :=
    freshDyson_eq_of_isDysonRoot hF hs (by simp) hm
  rw [e]; exact ⟨hm, hv⟩

/-- `t(x) = Tr M(x)M(E)`. -/
def realCross (F : Matrix (Fin N) (Fin N) ℂ) (s E x : ℝ) : ℂ :=
  (realResolvent F s x * realResolvent F s E).trace

theorem realResolvent_lipschitz (hF : F.IsHermitian) (hs : 0 < s) (hv₀ : 0 < v₀)
    (hR : RootRectangle F s E₀ r v₀) {x y : ℝ} (hx : |x - E₀| ≤ r) (hy : |y - E₀| ≤ r) :
    ‖realResolvent F s x - realResolvent F s y‖ ≤ resLip s v₀ * |x - y| := by
  obtain ⟨h₁, hv₁⟩ := realRoot_spec hF hs hR hx
  obtain ⟨h₂, hv₂⟩ := realRoot_spec hF hs hR hy
  have h := resolvent_lipschitz hF hs (by simp) (by simp) h₁ h₂ hv₀ hv₁ hv₂
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem tendsto_realResolvent (hF : F.IsHermitian) (hs : 0 < s) (hv₀ : 0 < v₀)
    (hR : RootRectangle F s E₀ r v₀) {E : ℝ} (hE : |E - E₀| < r) :
    Tendsto (realResolvent F s) (𝓝 E) (𝓝 (realResolvent F s E)) := by
  have hev : ∀ᶠ x in 𝓝 E, |x - E₀| ≤ r := by
    have ho : IsOpen {x : ℝ | |x - E₀| < r} :=
      isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
    filter_upwards [ho.mem_nhds hE] with x hx using le_of_lt hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun x : ℝ => resLip s v₀ * |x - E|) (𝓝 E) (𝓝 0) := by
    have hc : Continuous (fun x : ℝ => resLip s v₀ * |x - E|) := by fun_prop
    simpa using hc.tendsto E
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hev] with x hx
  exact realResolvent_lipschitz hF hs hv₀ hR hx hE.le

/-- The derivative of the real-axis root: `m'(E) = t/(N - s t)`, `t = Tr M(E)²`. -/
theorem hasDerivAt_realRoot (hF : F.IsHermitian) (hs : 0 < s) (hv₀ : 0 < v₀)
    (hR : RootRectangle F s E₀ r v₀) {E : ℝ} (hE : |E - E₀| < r) :
    HasDerivAt (realRoot F s)
      (realCross F s E E / ((N : ℂ) - s * realCross F s E E)) E := by
  have hev : ∀ᶠ x in 𝓝 E, |x - E₀| ≤ r := by
    have ho : IsOpen {x : ℝ | |x - E₀| < r} :=
      isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
    filter_upwards [ho.mem_nhds hE] with x hx using le_of_lt hx
  obtain ⟨hE₁, hvE⟩ := realRoot_spec hF hs hR hE.le
  have hden : ∀ x : ℝ, |x - E₀| ≤ r → (N : ℂ) - s * realCross F s E x ≠ 0 := by
    intro x hx
    obtain ⟨hx₁, hvx⟩ := realRoot_spec hF hs hR hx
    have h := stability_lower hF hs (by simp) (by simp) hx₁ hE₁ hv₀.le hvx hvE
    rw [Fintype.card_fin] at h
    intro h0
    unfold realCross realResolvent at h0
    rw [h0, norm_zero] at h
    have : 0 < 2 * s * (N : ℝ) * v₀ ^ 2 := by
      have : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
      positivity
    linarith
  have hcross : ∀ x : ℝ, realCross F s E x = (realResolvent F s x * realResolvent F s E).trace :=
    fun _ => rfl
  -- the cross trace tends to `Tr M(E)²`
  have ht : Tendsto (realCross F s E) (𝓝 E) (𝓝 (realCross F s E E)) := by
    have h1 := (tendsto_realResolvent hF hs hv₀ hR hE).mul_const (realResolvent F s E)
    exact ((continuous_id.matrix_trace).tendsto _).comp h1
  have hlim : Tendsto (fun x => realCross F s E x / ((N : ℂ) - s * realCross F s E x)) (𝓝 E)
      (𝓝 (realCross F s E E / ((N : ℂ) - s * realCross F s E E))) :=
    ht.div (tendsto_const_nhds.sub (tendsto_const_nhds.mul ht)) (hden E hE.le)
  rw [hasDerivAt_iff_tendsto_slope]
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with x hx hxE
  obtain ⟨hx₁, -⟩ := realRoot_spec hF hs hR hx
  have hid := dyson_diff_identity hF hs (by simp) (by simp) hx₁ hE₁
  rw [Fintype.card_fin] at hid
  have hxE' : ((x : ℂ) - (E : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_sub, Complex.ofReal_ne_zero, sub_ne_zero]; exact hxE
  have hd := hden x hx
  unfold realCross realResolvent at hd ⊢
  symm
  rw [slope_def_module, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_sub, eq_div_iff hd,
    mul_assoc, hid, ← mul_assoc, inv_mul_cancel₀ hxE', one_mul]

/-- The derivative of the boundary resolvent: `M'(E) = (1 + s m'(E)) M(E)²`. -/
theorem hasDerivAt_realResolvent (hF : F.IsHermitian) (hs : 0 < s) (hv₀ : 0 < v₀)
    (hR : RootRectangle F s E₀ r v₀) {E : ℝ} (hE : |E - E₀| < r) :
    HasDerivAt (realResolvent F s)
      ((1 + (s : ℂ) * (realCross F s E E / ((N : ℂ) - s * realCross F s E E))) •
        (realResolvent F s E * realResolvent F s E)) E := by
  have hev : ∀ᶠ x in 𝓝 E, |x - E₀| ≤ r := by
    have ho : IsOpen {x : ℝ | |x - E₀| < r} :=
      isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
    filter_upwards [ho.mem_nhds hE] with x hx using le_of_lt hx
  obtain ⟨hE₁, hvE⟩ := realRoot_spec hF hs hR hE.le
  have hm := hasDerivAt_realRoot hF hs hv₀ hR hE
  rw [hasDerivAt_iff_tendsto_slope] at hm ⊢
  have hM := tendsto_realResolvent hF hs hv₀ hR hE
  have hlim : Tendsto (fun x => (1 + (s : ℂ) * slope (realRoot F s) E x) •
      (realResolvent F s x * realResolvent F s E)) (𝓝[≠] E)
      (𝓝 ((1 + (s : ℂ) * (realCross F s E E / ((N : ℂ) - s * realCross F s E E))) •
        (realResolvent F s E * realResolvent F s E))) := by
    refine Tendsto.smul (tendsto_const_nhds.add (tendsto_const_nhds.mul hm)) ?_
    exact (hM.mono_left nhdsWithin_le_nhds).mul_const _
  refine hlim.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with x hx hxE
  obtain ⟨hx₁, hvx⟩ := realRoot_spec hF hs hR hx
  have hw₁ := (dysonRoot_w_im_pos (z := (x : ℂ)) hs (by simp) hx₁.1).ne'
  have hw₂ := (dysonRoot_w_im_pos (z := (E : ℂ)) hs (by simp) hE₁.1).ne'
  have hxE' : ((x - E : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, sub_ne_zero]; exact hxE
  symm
  rw [slope_def_module, slope_def_module, Complex.real_smul]
  unfold realResolvent
  rw [resolvent_sub hF hw₁ hw₂, ← Complex.coe_smul, smul_smul]
  congr 1
  rw [Complex.ofReal_inv]
  field_simp
  push_cast
  ring

/-- **The regular window of the external ETH theorem** from a
root rectangle: under `MDEBranchIdentification`, for Hermitian `F` on `Fin N`
(`N > 0`), `s > 0`, `v₀ > 0` and `RootRectangle F s E₀ r v₀`, every branch `M` of `F` at
`λ = √s` satisfies `RegularWindow M E₀ r K` for every `K ≥ regK s v₀`; the boundary values are
`realResolvent F s`.
-/
theorem regularWindow_of_rootRectangle (hMDE : MDEBranchIdentification)
    {F : CEH.SourceHermitian N} (hs : 0 < s) (hv₀ : 0 < v₀)
    (hR : RootRectangle F.1 s E₀ r v₀) {K : ℝ} (hK : regK s v₀ ≤ K)
    (M : CEH.MDEBranch (Real.sqrt s) F) : RegularWindow M E₀ r K := by
  have hF := F.2
  have hmem : ∀ E ∈ Ioo (E₀ - r) (E₀ + r), |E - E₀| < r := by
    intro E hE; rw [abs_sub_lt_iff]; constructor <;> linarith [hE.1, hE.2]
  refine ⟨realResolvent F.1 s, fun E hE => ?_, fun E hE => ?_, fun E hE => ?_⟩
  · -- boundary values
    have hE' := hmem E hE
    obtain ⟨hE₁, hvE⟩ := realRoot_spec hF hs hR hE'.le
    have hbound : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), ‖M.matrix ((E : ℂ) + (η : ℂ) * Complex.I) -
        realResolvent F.1 s E‖ ≤ resLip s v₀ * η := by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with η hη
      obtain ⟨m, hm, hv⟩ := hR E hE'.le η hη.1.le hη.2.le
      have hz : 0 < ((E : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη.1
      have hmeq := (isDysonRoot_iff _ _ _ _).mp hm
      obtain ⟨hb, -⟩ := BlockBand.LocalWindow.ProofCertificate.branch_eq_of_root hMDE
        (NeZero.pos N) hs F M hz hm.1 hmeq.2
      rw [hb]
      have h := resolvent_lipschitz hF hs hz.le (by simp) hm hE₁ hv₀ hv hvE
      have e : ‖((E : ℂ) + (η : ℂ) * Complex.I) - (E : ℂ)‖ = η := by
        simp [abs_of_pos hη.1]
      rw [e] at h
      exact h
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun η : ℝ => resLip s v₀ * η) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun η : ℝ => resLip s v₀ * η) := by fun_prop
      exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hc.tendsto 0)
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hlim
  · exact (hasDerivAt_realResolvent hF hs hv₀ hR (hmem E hE)).differentiableAt.differentiableWithinAt
  · have hE' := hmem E hE
    obtain ⟨hE₁, hvE⟩ := realRoot_spec hF hs hR hE'.le
    have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    have hMn : ‖realResolvent F.1 s E‖ ≤ (s * v₀)⁻¹ :=
      opNorm_root_resolvent_le hF hs (by simp) hv₀ hvE
    have hstab := stability_lower hF hs (by simp) (by simp) hE₁ hE₁ hv₀.le hvE hvE
    rw [Fintype.card_fin] at hstab
    have htr := norm_trace_mul_roots_le hF hs (by simp) (by simp) hE₁ hE₁
    rw [Fintype.card_fin] at htr
    set t := realCross F.1 s E E with ht
    have hstab' : 2 * s * N * v₀ ^ 2 ≤ ‖(N : ℂ) - s * t‖ := hstab
    have htr' : s * ‖t‖ ≤ N := htr
    have hpos : 0 < 2 * s * N * v₀ ^ 2 := by positivity
    have hden : 0 < ‖(N : ℂ) - s * t‖ := hpos.trans_le hstab'
    -- `|m'| ≤ L`
    have hder : ‖t / ((N : ℂ) - s * t)‖ ≤ rootLip s v₀ := by
      rw [norm_div, div_le_iff₀ hden]
      unfold rootLip
      have : ‖t‖ ≤ N / s := by rw [le_div_iff₀ hs]; linarith
      calc ‖t‖ ≤ N / s := this
        _ = (2 * s ^ 2 * v₀ ^ 2)⁻¹ * (2 * s * N * v₀ ^ 2) := by field_simp
        _ ≤ (2 * s ^ 2 * v₀ ^ 2)⁻¹ * ‖(N : ℂ) - s * t‖ :=
          mul_le_mul_of_nonneg_left hstab' (by positivity)
    have hKpos : 0 < K := by
      refine lt_of_lt_of_le ?_ hK
      unfold regK
      exact lt_of_lt_of_le (inv_pos.mpr hv₀) ((le_max_left _ _).trans (le_max_right _ _))
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [(hasDerivAt_realResolvent hF hs hv₀ hR hE').deriv, norm_smul]
      refine le_trans ?_ ((le_max_left _ _).trans ((le_max_left _ _).trans hK))
      unfold resLip
      have h1 : ‖(1 : ℂ) + (s : ℂ) * (t / ((N : ℂ) - s * t))‖ ≤ 1 + s * rootLip s v₀ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
        nlinarith [mul_le_mul_of_nonneg_left hder hs.le]
      have h2 : ‖realResolvent F.1 s E * realResolvent F.1 s E‖ ≤ ((s * v₀)⁻¹) ^ 2 := by
        refine (norm_mul_le _ _).trans ?_
        rw [sq]
        exact mul_le_mul hMn hMn (norm_nonneg _) (inv_nonneg.mpr (mul_pos hs hv₀).le)
      exact mul_le_mul h1 h2 (norm_nonneg _) (by have := rootLip_nonneg s v₀; positivity)
    · exact hMn.trans ((le_max_right _ _).trans ((le_max_left _ _).trans hK))
    · have htrace : CEH.normalizedTrace (realResolvent F.1 s E) = realRoot F.1 s E := by
        have := hE₁.2
        rw [Fintype.card_fin] at this
        unfold CEH.normalizedTrace realResolvent
        exact this.symm
      rw [htrace]
      have hK1 : v₀⁻¹ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
      calc 1 / K ≤ 1 / v₀⁻¹ := one_div_le_one_div_of_le (inv_pos.mpr hv₀) hK1
        _ = v₀ := by rw [one_div, inv_inv]
        _ ≤ _ := hvE
    · have hK2 : (2 * s * v₀ ^ 2)⁻¹ ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
      have e : (1 : ℂ) - (s : ℂ) * CEH.normalizedTrace
          (realResolvent F.1 s E * realResolvent F.1 s E) = (N : ℂ)⁻¹ * ((N : ℂ) - s * t) := by
        unfold CEH.normalizedTrace
        rw [ht]
        unfold realCross
        have : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.pos N).ne'
        field_simp
      rw [e, norm_mul, norm_inv, Complex.norm_natCast]
      have hpos2 : 0 < 2 * s * v₀ ^ 2 := by positivity
      calc 1 / K ≤ 1 / (2 * s * v₀ ^ 2)⁻¹ := one_div_le_one_div_of_le (inv_pos.mpr hpos2) hK2
        _ = 2 * s * v₀ ^ 2 := by rw [one_div, inv_inv]
        _ ≤ (N : ℝ)⁻¹ * ‖(N : ℂ) - s * t‖ := by
          rw [inv_mul_eq_div, le_div_iff₀ hN]; linarith

/-- `regK` is antitone in the variance: `regK s₂ v₀ ≤ regK s₁ v₀` for `0 < s₁ ≤ s₂`. -/
theorem regK_anti {s₁ s₂ v₀ : ℝ} (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂) (hv₀ : 0 < v₀) :
    regK s₂ v₀ ≤ regK s₁ v₀ := by
  have hs₂ : 0 < s₂ := hs₁.trans_le hs
  have h1 : (s₂ * v₀)⁻¹ ≤ (s₁ * v₀)⁻¹ :=
    inv_anti₀ (mul_pos hs₁ hv₀) (mul_le_mul_of_nonneg_right hs hv₀.le)
  have h2 : (2 * s₂ * v₀ ^ 2)⁻¹ ≤ (2 * s₁ * v₀ ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (by nlinarith [sq_nonneg v₀])
  have h3 : s₂ * rootLip s₂ v₀ ≤ s₁ * rootLip s₁ v₀ := by
    unfold rootLip
    have e : ∀ s : ℝ, 0 < s → s * (2 * s ^ 2 * v₀ ^ 2)⁻¹ = (2 * s * v₀ ^ 2)⁻¹ := by
      intro s hs; field_simp
    rw [e s₂ hs₂, e s₁ hs₁]; exact h2
  have h4 : resLip s₂ v₀ ≤ resLip s₁ v₀ := by
    unfold resLip
    have hr := rootLip_nonneg s₂ v₀
    exact mul_le_mul (by linarith) (pow_le_pow_left₀ (inv_nonneg.mpr (by positivity)) h1 2)
      (by positivity) (by have := rootLip_nonneg s₁ v₀; positivity)
  unfold regK
  exact max_le_max (max_le_max h4 h1) (max_le_max le_rfl h2)

end RealLine

/-!
## The root rectangle from the pole certificate
-/

section Certificate

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.ProofCertificate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Spectral shift: `m` is a root of `F - c` at `z` iff it is a root of `F` at `z + c`. -/
theorem isDysonRoot_sub_smul (F : Matrix ι ι ℂ) (s : ℝ) (c z m : ℂ) :
    IsDysonRoot (F - c • (1 : Matrix ι ι ℂ)) s z m ↔ IsDysonRoot F s (z + c) m := by
  unfold IsDysonRoot
  have e : F - c • (1 : Matrix ι ι ℂ) - (z + (s : ℂ) * m) • (1 : Matrix ι ι ℂ) =
      F - (z + c + (s : ℂ) * m) • (1 : Matrix ι ι ℂ) := by
    rw [sub_sub, ← add_smul]; congr 2; ring
  rw [e]

/-- A root rectangle on any index type gives `RootRectangle` after reindexing by `Fin`. -/
theorem rootRectangle_reindex {N : ℕ} [NeZero N] (e : ι ≃ Fin N) {K : Matrix ι ι ℂ}
    {s E₀ r v₀ : ℝ}
    (h : ∀ x : ℝ, |x - E₀| ≤ r → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
      ∃ m : ℂ, IsDysonRoot K s ((x : ℂ) + (η : ℂ) * Complex.I) m ∧ v₀ ≤ m.im) :
    RootRectangle (reindex e e K) s E₀ r v₀ := by
  intro x hx η hη hη1
  obtain ⟨m, hm, hv⟩ := h x hx η hη hη1
  exact ⟨m, (isDysonRoot_reindex e K s _ m).mpr hm, hv⟩

/-- **Root rectangle from the uniform pole certificate** (the uniform pole certificate and its
regularity consequence, through `ProofCertificate.poleCertificate_regular`): fixed `b ∈ (0, 1/2)`, `κ > 0` first; then
constants `ε_c, r, s₀, v₀ > 0`; for every admissible `p` with `p.b = b`, split state with
Hermitian `V`, truncation radius `ε`, `e ∈ bulkInterval κ` with `certErrHat ε p i ω e ≤ ε_c` and
`s' ∈ [s - s₀, s]` (`s = splitS p`; this includes the compressed variance `s(1 - 1/d)` for large
`W`): at every `x + iη`, `|x - e| ≤ r`, `0 ≤ η ≤ 1`, the truncated
deformation `F̂(e)` has a Dyson root with `Im m ≥ v₀`. -/
theorem rootRectangle_of_poleCertificate (b κ : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ εc r s₀ v₀ : ℝ, 0 < εc ∧ 0 < r ∧ 0 < s₀ ∧ 0 < v₀ ∧
      ∀ p : BlockBand.Parameters, p.b = b → ∀ (i : ZMod p.n) (om : SplitState p i)
        (_hV : om.2.2.IsHermitian) (ε e : ℝ), e ∈ bulkInterval κ → certErrHat ε p i om e ≤ εc →
        ∀ s' : ℝ, splitS p - s₀ ≤ s' → s' ≤ splitS p →
          ∀ x : ℝ, |x - e| ≤ r → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
            ∃ m : ℂ, IsDysonRoot (truncF ε om.1 om.2.1 om.2.2 e) s'
              ((x : ℂ) + (η : ℂ) * Complex.I) m ∧ v₀ ≤ m.im := by
  obtain ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, h⟩ := poleCertificate_regular b κ hb hb' hκ
  refine ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, fun p hpb i om hV ε e he hcert s' hs1 hs2 x hx η hη
    hη1 => ?_⟩
  obtain ⟨heq, hlo, -⟩ := h p hpb i om hV ε e he hcert s' hs1 hs2 x hx η hη hη1
  refine ⟨_, ?_, hlo⟩
  rw [isDysonRoot_iff, mul_comm (η : ℂ) Complex.I]
  exact ⟨hv₀.trans_le hlo, heq⟩

end Certificate

end BlockBand.LocalWindow.ProofETH
