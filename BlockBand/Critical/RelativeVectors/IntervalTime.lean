module

public import BlockBand.Critical.RelativeVectors.Coarse
public import BlockBand.Critical.RelativeVectors.Polarize
public import BlockBand.Critical.RelativeVectors.CovShift

/-!
# The interval bounds at one time from a mesh time

Deterministic. *Domain:* `N ≥ 1`, `FreshConstants c r₀ s₀ v₀`, `F` in `FreshClass`, a frame `V`
with `V^*ΓV = I_r`, times `s, σ ∈ [c - s₀, c]`, Hermitian `H` (time `s`) and `H'` (time `σ`),
`h = N^{-1/100}`.

* `interval_time_bounds`: if `H'` is `MeshGood` for `Q = polFrame V`, `‖H - H'‖ ≤ h³`,
  `‖H - H'‖ N^{2max(A,1)}/(v₀ lowConst) ≤ h³` and `|s - σ| ≤ h`, then for every `|x - E| ≤ r₀/2`
  and `p ∈ ℂ^r`, with `w = Vp`, `G = (H - z)⁻¹`:
  1. `Im w^*G(x+iη)w ≤ B₁‖p‖²` for `h ≤ η ≤ 1`;
  2. `Im Tr G(x+iη) ≤ N B₂` for `h ≤ η ≤ 1`;
  3. `|N Im w^*G(x+ih)w - φ_s(x) Im Tr G(x+ih)| ≤ N B₃ h ‖p‖²`, `φ_s(x) = w^*Γ(s,x)w`.

  Proof of 3: move from `H` to `H'` (resolvent comparison), use the isotropic law at `σ`
  (polarized in `V`, `frame_quad_le_of_pol`) and the scalar law at `σ`, then the deterministic
  shifts `η = h → 0` and `σ → s` of the covariance weight (`phi_eta_shift`, `phi_time_shift`).
  `N^{-1/3} ≤ h`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.MomentFlow BlockBand.Palm.CoarseRelative BlockBand.Palm.GoodEvent
open BlockBand.Critical.WeightedDensity

variable {N r : ℕ}

/-- `Im w^*(H - z)⁻¹w`. -/
def rIm (H : Matrix (Fin N) (Fin N) ℂ) (w : Fin N → ℂ) (z : ℂ) : ℝ :=
  (star w ⬝ᵥ ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ w)).im

/-- `Im Tr (H - z)⁻¹`. -/
def rTr (H : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) : ℝ :=
  ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace.im

/-- The two bounds of `CoarseRelativeContract` for `H'` at variance `σ` and family `Q`. -/
def MeshGood (F : Matrix (Fin N) (Fin N) ℂ) (E r₀ σ : ℝ) (Q : Finset (Fin N → ℂ))
    (H' : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ x η : ℝ, |x - E| ≤ r₀ / 2 → (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η → η ≤ 1 →
    ‖(N : ℂ)⁻¹ * ((H' - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace -
        freshDyson F σ ⟨x, η⟩‖ ≤ (N : ℝ) ^ (-(1 / 3 : ℝ)) ∧
      ∀ q ∈ Q, ‖star q ⬝ᵥ (((H' - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
          freshM F σ ⟨x, η⟩) *ᵥ q)‖ ≤
        (N : ℝ) ^ (-(1 / 3 : ℝ)) * (star q ⬝ᵥ (freshM F σ ⟨x, η⟩ *ᵥ q)).im

theorem meshGood_of_not_coarseBad {F G : Matrix (Fin N) (Fin N) ℂ} {E r₀ σ : ℝ}
    {Q : Finset (Fin N → ℂ)} (hG : G ∉ coarseBadSet F E r₀ σ Q) :
    MeshGood F E r₀ σ Q (F + (Real.sqrt σ : ℂ) • G) := by
  intro x η hx hη hη1
  constructor
  · by_contra h
    exact hG ⟨x, η, hx, hη, hη1, Or.inl (lt_of_not_ge h)⟩
  · intro q hq
    by_contra h
    exact hG ⟨x, η, hx, hη, hη1, Or.inr ⟨q, hq, lt_of_not_ge h⟩⟩

theorem trace_im_eq_sum (X : Matrix (Fin N) (Fin N) ℂ) :
    X.trace.im = ∑ k, (star (Pi.single k (1 : ℂ)) ⬝ᵥ (X *ᵥ Pi.single k 1)).im := by
  rw [Matrix.trace, Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mulVec_single_one]
  simp [dotProduct, Pi.single_apply]

theorem nsq_single (k : Fin N) : nsq (Pi.single k (1 : ℂ) : Fin N → ℂ) = 1 := by
  unfold nsq
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem rIm_compare {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (w : Fin N → ℂ) :
    |rIm H w z - rIm H' w z| ≤ opB (H - H') * nsq w / z.im ^ 2 := by
  have h1 := resolvent_quad_im_compare hH hH' hz w
  have h2 := resolvent_quad_im_compare hH' hH hz w
  rw [show H' - H = -(H - H') by abel, opB_neg] at h2
  unfold rIm
  rw [abs_le]; constructor <;> linarith

theorem rTr_compare {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    |rTr H z - rTr H' z| ≤ N * (opB (H - H') / z.im ^ 2) := by
  unfold rTr
  rw [trace_im_eq_sum, trace_im_eq_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ k : Fin N, |(star (Pi.single k (1 : ℂ)) ⬝ᵥ
      ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ Pi.single k 1)).im -
      (star (Pi.single k (1 : ℂ)) ⬝ᵥ
      ((H' - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ Pi.single k 1)).im| ≤
        opB (H - H') / z.im ^ 2 := by
    intro k
    have := rIm_compare hH hH' hz (Pi.single k 1)
    rw [nsq_single, mul_one] at this
    exact this
  refine (Finset.sum_le_sum fun k _ => this k).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `B₁ = K + 4Kr + 1`. -/
def intB1 (c r₀ s₀ v₀ : ℝ) (r : ℕ) : ℝ :=
  gammaCompConst c r₀ s₀ v₀ + 4 * gammaCompConst c r₀ s₀ v₀ * r + 1

/-- `B₂ = v₀⁻¹ + 2`. -/
def intB2 (v₀ : ℝ) : ℝ := v₀⁻¹ + 2

/-- `B₃ = 1 + 4Kr + C_c + C_d v₀⁻¹ + 2C_φ`. -/
def intB3 (c r₀ s₀ v₀ : ℝ) (r : ℕ) : ℝ :=
  1 + 4 * gammaCompConst c r₀ s₀ v₀ * r +
    (dysonGammaConst c r₀ s₀ v₀ +
      c * v₀⁻¹ * dysonShiftConst c r₀ s₀ v₀ * dysonGammaConst c r₀ s₀ v₀) +
    (1 + c * dysonShiftConst c r₀ s₀ v₀) * dysonGammaConst c r₀ s₀ v₀ * v₀⁻¹ +
    2 * (c * dysonGammaConst c r₀ s₀ v₀)

theorem rpow_third_le_hundredth {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)

/-- **The interval bounds at one time.** See the module docstring. -/
theorem interval_time_bounds {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {V : Matrix (Fin N) (Fin r) ℂ} (hV : Vᴴ * freshGamma F c E * V = 1) {s σ : ℝ}
    (hs : s ∈ Icc (c - s₀) c) (hσ : σ ∈ Icc (c - s₀) c) {H H' : Matrix (Fin N) (Fin N) ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) (hgood : MeshGood F E r₀ σ (polFrame V) H')
    (hΔ : opB (H - H') * ((N : ℝ) ^ (2 * max A 1) / (v₀ * lowConst c s₀ v₀)) ≤
      ((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 3)
    (hΔ' : opB (H - H') ≤ ((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 3)
    (hsσ : |s - σ| ≤ (N : ℝ) ^ (-(1 / 100 : ℝ))) (x : ℝ) (hx : |x - E| ≤ r₀ / 2) :
    (∀ η : ℝ, (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η → η ≤ 1 → ∀ p : Fin r → ℂ,
      rIm H (V *ᵥ p) ⟨x, η⟩ ≤ intB1 c r₀ s₀ v₀ r * nsq p) ∧
    (∀ η : ℝ, (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η → η ≤ 1 → rTr H ⟨x, η⟩ ≤ N * intB2 v₀) ∧
    ∀ p : Fin r → ℂ, |(N : ℝ) * rIm H (V *ᵥ p) ⟨x, (N : ℝ) ^ (-(1 / 100 : ℝ))⟩ -
        quadForm (freshGamma F s x) (V *ᵥ p) * rTr H ⟨x, (N : ℝ) ^ (-(1 / 100 : ℝ))⟩| ≤
      N * intB3 c r₀ s₀ v₀ r * (N : ℝ) ^ (-(1 / 100 : ℝ)) * nsq p := by
  have hK' := hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK'
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set h := (N : ℝ) ^ (-(1 / 100 : ℝ)) with hhdef
  have hh : 0 < h := Real.rpow_pos_of_pos hNr _
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  have h13 := rpow_third_le_hundredth hN
  rw [← hhdef] at h13
  set n3 := (N : ℝ) ^ (-(1 / 3 : ℝ)) with hn3
  have hn30 : 0 ≤ n3 := (Real.rpow_pos_of_pos hNr _).le
  set Δ := opB (H - H') with hΔdef
  have hΔ0 : 0 ≤ Δ := opB_nonneg _
  set Kc := gammaCompConst c r₀ s₀ v₀ with hKc
  have hKc0 : 0 < Kc := gammaCompConst_pos hK
  have hL := lowConst_pos' hK
  have hxr : |x - E| ≤ r₀ := by linarith
  -- perturbation bounds
  have hpertW : ∀ (η : ℝ), h ≤ η → ∀ p : Fin r → ℂ,
      Δ * nsq (V *ᵥ p) / η ^ 2 ≤ h * nsq p := by
    intro η hη p
    have hn := nsq_le_of_gamma hN hK hC (V *ᵥ p)
    rw [quadForm_frame hV] at hn
    have hηpos : 0 < η := lt_of_lt_of_le hh hη
    have hp0 := nsq_nonneg p
    have h1 : Δ * nsq (V *ᵥ p) ≤ h ^ 3 * nsq p := by
      calc Δ * nsq (V *ᵥ p) ≤ Δ * ((N : ℝ) ^ (2 * max A 1) * nsq p / (v₀ * lowConst c s₀ v₀)) :=
            mul_le_mul_of_nonneg_left hn hΔ0
        _ = Δ * ((N : ℝ) ^ (2 * max A 1) / (v₀ * lowConst c s₀ v₀)) * nsq p := by ring
        _ ≤ h ^ 3 * nsq p := mul_le_mul_of_nonneg_right hΔ hp0
    have h2 : h ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hh.le hη 2
    rw [div_le_iff₀ (by positivity)]
    calc Δ * nsq (V *ᵥ p) ≤ h ^ 3 * nsq p := h1
      _ = h * nsq p * h ^ 2 := by ring
      _ ≤ h * nsq p * η ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hpertT : ∀ (η : ℝ), h ≤ η → Δ / η ^ 2 ≤ h := by
    intro η hη
    have hηpos : 0 < η := lt_of_lt_of_le hh hη
    have h2 : h ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hh.le hη 2
    rw [div_le_iff₀ (by positivity)]
    calc Δ ≤ h ^ 3 := hΔ'
      _ = h * h ^ 2 := by ring
      _ ≤ h * η ^ 2 := mul_le_mul_of_nonneg_left h2 hh.le
  -- the mesh-time bounds
  have hmesh : ∀ η : ℝ, h ≤ η → η ≤ 1 →
      |rTr H' ⟨x, η⟩ - N * (freshDyson F σ ⟨x, η⟩).im| ≤ N * n3 ∧
      ∀ p : Fin r → ℂ, |rIm H' (V *ᵥ p) ⟨x, η⟩ - (star (V *ᵥ p) ⬝ᵥ
        (freshM F σ ⟨x, η⟩ *ᵥ (V *ᵥ p))).im| ≤ 4 * Kc * n3 * r * nsq p := by
    intro η hη hη1
    obtain ⟨htr, hq⟩ := hgood x η hx hη hη1
    constructor
    · have e : rTr H' ⟨x, η⟩ - N * (freshDyson F σ ⟨x, η⟩).im = N *
          ((N : ℂ)⁻¹ * ((H' - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace -
            freshDyson F σ ⟨x, η⟩).im := by
        unfold rTr
        rw [Complex.sub_im, show ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
          Complex.im_ofReal_mul]
        field_simp
      rw [e, abs_mul, abs_of_pos hNr]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans htr) hNr.le
    · intro p
      have hpol := frame_quad_le_of_pol V
        ((H' - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - freshM F σ ⟨x, η⟩)
        (β := 4 * Kc * n3) (fun q hqm => by
          refine (hq q hqm).trans ?_
          have hm := quad_im_le_gamma hN hK hC hσ (z := ⟨x, η⟩) hxr
            (le_trans hh.le hη) hη1 q
          have h4 := quadForm_polFrame_le hV hqm
          have hG0 := quadForm_freshGamma_nonneg F hc0.le E q
          calc n3 * (star q ⬝ᵥ (freshM F σ ⟨x, η⟩ *ᵥ q)).im
              ≤ n3 * (Kc * quadForm (freshGamma F c E) q) := mul_le_mul_of_nonneg_left hm hn30
            _ ≤ n3 * (Kc * 4) := mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left h4 hKc0.le) hn30
            _ = 4 * Kc * n3 := by ring) p
      have e : rIm H' (V *ᵥ p) ⟨x, η⟩ - (star (V *ᵥ p) ⬝ᵥ (freshM F σ ⟨x, η⟩ *ᵥ (V *ᵥ p))).im =
          (star (V *ᵥ p) ⬝ᵥ (((H' - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
            freshM F σ ⟨x, η⟩) *ᵥ (V *ᵥ p))).im := by
        unfold rIm
        rw [sub_mulVec, dotProduct_sub, Complex.sub_im]
      rw [e]
      exact (Complex.abs_im_le_norm _).trans hpol
  -- (1) and (2)
  have hM : ∀ η : ℝ, h ≤ η → η ≤ 1 → ∀ p : Fin r → ℂ,
      (star (V *ᵥ p) ⬝ᵥ (freshM F σ ⟨x, η⟩ *ᵥ (V *ᵥ p))).im ≤ Kc * nsq p := by
    intro η hη hη1 p
    have := quad_im_le_gamma hN hK hC hσ (z := ⟨x, η⟩) hxr (le_trans hh.le hη) hη1 (V *ᵥ p)
    rwa [quadForm_frame hV] at this
  have hmb : ∀ η : ℝ, h ≤ η → η ≤ 1 → (freshDyson F σ ⟨x, η⟩).im ≤ v₀⁻¹ := fun η hη hη1 =>
    (fresh_regular_bounds hC.2.2 hσ (z := ⟨x, η⟩) hxr (le_trans hh.le hη) hη1).2
  have hHH' : ∀ η : ℝ, h ≤ η → ∀ p : Fin r → ℂ,
      |rIm H (V *ᵥ p) ⟨x, η⟩ - rIm H' (V *ᵥ p) ⟨x, η⟩| ≤ h * nsq p := by
    intro η hη p
    have hηpos : 0 < η := lt_of_lt_of_le hh hη
    exact (rIm_compare hH hH' (z := ⟨x, η⟩) hηpos (V *ᵥ p)).trans (hpertW η hη p)
  have hHH'T : ∀ η : ℝ, h ≤ η → |rTr H ⟨x, η⟩ - rTr H' ⟨x, η⟩| ≤ N * h := by
    intro η hη
    have hηpos : 0 < η := lt_of_lt_of_le hh hη
    exact (rTr_compare hH hH' (z := ⟨x, η⟩) hηpos).trans
      (mul_le_mul_of_nonneg_left (hpertT η hη) hNr.le)
  refine ⟨fun η hη hη1 p => ?_, fun η hη hη1 => ?_, fun p => ?_⟩
  · have h1 := (abs_le.1 (hHH' η hη p)).2
    have h2 := (abs_le.1 ((hmesh η hη hη1).2 p)).2
    have h3 := hM η hη hη1 p
    have hp0 := nsq_nonneg p
    have hn31 : n3 ≤ 1 := h13.trans hh1
    have : 4 * Kc * n3 * r * nsq p ≤ 4 * Kc * r * nsq p := by
      have : 0 ≤ 4 * Kc * r * nsq p := by positivity
      nlinarith
    have : h * nsq p ≤ nsq p := by nlinarith
    unfold intB1
    nlinarith
  · have h1 := (abs_le.1 (hHH'T η hη)).2
    have h2 := (abs_le.1 (hmesh η hη hη1).1).2
    have h3 := hmb η hη hη1
    have hn31 : n3 ≤ 1 := h13.trans hh1
    unfold intB2
    nlinarith
  · -- the main comparison at height h
    have hhh : h ≤ h := le_rfl
    set w := V *ᵥ p with hw
    set φs := quadForm (freshGamma F s x) w
    set φσ := quadForm (freshGamma F σ x) w
    set mi := (freshDyson F σ ⟨x, h⟩).im
    set iM := (star w ⬝ᵥ (freshM F σ ⟨x, h⟩ *ᵥ w)).im
    have hp0 := nsq_nonneg p
    have hΓw : quadForm (freshGamma F c E) w = nsq p := quadForm_frame hV p
    have hφs0 : 0 ≤ φs := quadForm_freshGamma_nonneg F (le_trans (by linarith) hs.1) x w
    have hφs := phi_le hN hK hC hs hxr w
    rw [hΓw] at hφs
    have hmi0 : 0 ≤ mi := hv0.le.trans
      (fresh_regular_bounds hC.2.2 hσ (z := ⟨x, h⟩) hxr hh.le hh1).1
    have hmi1 := hmb h hhh hh1
    have hTa := hHH' h hhh p
    have hTb := (hmesh h hhh hh1).2 p
    have hTc := phi_eta_shift hN hK hC hσ hxr hh hh1 w
    rw [hΓw] at hTc
    have hTd := phi_time_shift hN hK hC hs hσ hxr w
    rw [hΓw, abs_sub_comm σ s] at hTd
    have hTe := (hmesh h hhh hh1).1
    have hTf := hHH'T h hhh
    set Cp := c * dysonGammaConst c r₀ s₀ v₀ with hCp
    have hCp0 : 0 ≤ Cp := by
      rw [hCp]; unfold dysonGammaConst; have := dysonShiftConst_nonneg hK; positivity
    have hCpn : 0 ≤ Cp * nsq p := mul_nonneg hCp0 hp0
    set Cc := dysonGammaConst c r₀ s₀ v₀ +
      c * v₀⁻¹ * dysonShiftConst c r₀ s₀ v₀ * dysonGammaConst c r₀ s₀ v₀
    set Cd := (1 + c * dysonShiftConst c r₀ s₀ v₀) * dysonGammaConst c r₀ s₀ v₀
    have hCd0 : 0 ≤ Cd := by
      have := dysonShiftConst_nonneg hK
      have : 0 ≤ dysonGammaConst c r₀ s₀ v₀ := by
        unfold dysonGammaConst; have := dysonShiftConst_nonneg hK; positivity
      positivity
    -- decomposition
    have e : (N : ℝ) * rIm H w ⟨x, h⟩ - φs * rTr H ⟨x, h⟩ =
        N * (rIm H w ⟨x, h⟩ - rIm H' w ⟨x, h⟩) + N * (rIm H' w ⟨x, h⟩ - iM) +
        N * (iM - φσ * mi) + N * ((φσ - φs) * mi) + φs * (N * mi - rTr H' ⟨x, h⟩) +
        φs * (rTr H' ⟨x, h⟩ - rTr H ⟨x, h⟩) := by ring
    rw [e]
    have b1 : |(N : ℝ) * (rIm H w ⟨x, h⟩ - rIm H' w ⟨x, h⟩)| ≤ N * (h * nsq p) := by
      rw [abs_mul, abs_of_pos hNr]; exact mul_le_mul_of_nonneg_left hTa hNr.le
    have b2 : |(N : ℝ) * (rIm H' w ⟨x, h⟩ - iM)| ≤ N * (4 * Kc * r * h * nsq p) := by
      rw [abs_mul, abs_of_pos hNr]
      refine mul_le_mul_of_nonneg_left (hTb.trans ?_) hNr.le
      have : 0 ≤ 4 * Kc * r * nsq p := by positivity
      nlinarith
    have b3 : |(N : ℝ) * (iM - φσ * mi)| ≤ N * (Cc * h * nsq p) := by
      rw [abs_mul, abs_of_pos hNr]; exact mul_le_mul_of_nonneg_left hTc hNr.le
    have b4 : |(N : ℝ) * ((φσ - φs) * mi)| ≤ N * (Cd * v₀⁻¹ * h * nsq p) := by
      rw [abs_mul, abs_of_pos hNr, abs_mul, abs_of_nonneg hmi0]
      refine mul_le_mul_of_nonneg_left ?_ hNr.le
      calc |φσ - φs| * mi ≤ (Cd * |s - σ| * nsq p) * v₀⁻¹ :=
            mul_le_mul hTd hmi1 hmi0 (by positivity)
        _ ≤ (Cd * h * nsq p) * v₀⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsσ hCd0) hp0
        _ = Cd * v₀⁻¹ * h * nsq p := by ring
    have b5 : |φs * (N * mi - rTr H' ⟨x, h⟩)| ≤ N * (Cp * h * nsq p) := by
      rw [abs_mul, abs_of_nonneg hφs0, abs_sub_comm]
      calc φs * |rTr H' ⟨x, h⟩ - N * mi| ≤ (Cp * nsq p) * (N * n3) :=
            mul_le_mul hφs hTe (abs_nonneg _) hCpn
        _ ≤ (Cp * nsq p) * (N * h) := by
            apply mul_le_mul_of_nonneg_left _ hCpn
            exact mul_le_mul_of_nonneg_left h13 hNr.le
        _ = N * (Cp * h * nsq p) := by ring
    have b6 : |φs * (rTr H' ⟨x, h⟩ - rTr H ⟨x, h⟩)| ≤ N * (Cp * h * nsq p) := by
      rw [abs_mul, abs_of_nonneg hφs0, abs_sub_comm]
      calc φs * |rTr H ⟨x, h⟩ - rTr H' ⟨x, h⟩| ≤ (Cp * nsq p) * (N * h) :=
            mul_le_mul hφs hTf (abs_nonneg _) hCpn
        _ = N * (Cp * h * nsq p) := by ring
    have htot := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5) b6
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl)
      le_rfl) le_rfl).trans ?_
    refine htot.trans (le_of_eq ?_)
    unfold intB3
    ring

end BlockBand.Critical.RelativeVectors
