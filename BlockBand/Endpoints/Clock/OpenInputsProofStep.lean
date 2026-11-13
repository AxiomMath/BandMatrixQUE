module

public import BlockBand.Endpoints.Clock.ZeroEntranceProb
public import BlockBand.Endpoints.Clock.ClockMixingAlgebra

/-!
# The open-inputs lemma: the deterministic one-step contraction

We prove the deterministic one-step contraction of the scalar and of the first jet (Steps 2–4 of
the paper's proof of the open-inputs lemma). For a Hermitian `X` (the old Schur matrix of the one-ended path)
let `f(ζ) = W⁻¹ Tr(ζ - X)⁻¹`, `a = matchedA E`, `z = boundaryZ b E`, `c = 1 - 2b`,
`k = c + b²a²` (`kMinus`), `δ₀ = |f(z) - a|` (`jetDistance0`), `δ₁ = |f'(z) - s|`
(`jetDistance1`). The cavity solution `(v, u)` of the cavity equations at the port `z`
(`cavityV`, `cavityU`, the cavity-mean lemma) satisfies, on a fixed scalar domain `δ₀ ≤ r₀`
(`step_bound`):
* Step 2 (scalar contraction): `|u - a| ≤ q δ₀`;
* Steps 3–4 (first jet): `|u'(z) - s| ≤ q δ₁ + C δ₀` at every stationary jet `s`
  (`IsStationaryJet`, the fixed point of `F(s) = -a²(1+cs)/(1+ks)`),
with `q < 1`, `r₀ > 0`, `C` depending only on `b, E`.

The proof follows the paper: the exact identities `u - a = abu(v - a)` and
`v - f(z) = K(ζ₀,z)(z - ζ₀)` (resolvent identity), `z - ζ₀ = c(v - a) + b(u - a)`, give
`(v - a)(1 - K(c + b²au)) = f(z) - a`; the kernel is bounded through the imaginary identity
`Σ_i p_i|ζ - x_i|⁻² = -Im f(ζ)/Im ζ` by `(1-b)⁻¹ + O(δ₀)` (the Stieltjes bound of Step 3), and
`(1-b)⁻¹|k| < 1 - b` (`norm_kMinus_lt`) is the strict contraction for one
block. The a priori bound `|v - a| + |u - a| ≤ C δ₀` is the stability theorem of
the cavity-mean lemma (`CavityMean.cavity_stability`). The jet uses the derivative of
`v` (`CavityMeanProb.cavitySol_hasDerivAt_v`) and the exact identities
`u' = Φ(u,t) = -u²(1+ct)/(1+(c+b²u²)t)`, `Φ(u,t) - F(t) = -(1+ct)²(u²-a²)/(…)`,
`F(t) - F(s) = a⁴b²(t-s)/((1+kt)(1+ks))` with `t = f'(ζ₀)` (Step 3: the first-jet equation;
Step 4: `|F'| ≤ q₁² < 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Complex Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath

namespace OpenInputsProof

open CavityMeanProb

section Kernel

variable {ι : Type} [Fintype ι] {p x : ι → ℝ}

/-- Termwise AM–GM for the mixed kernel: `|K(ζ, ζ')| ≤ (S(ζ) + S(ζ'))/2`. -/
theorem norm_kerK_le (hp : IsCavityWeights p) (ζ ζ' : ℂ) :
    ‖kerK p x ζ ζ'‖ ≤ (cavitySq p x ζ + cavitySq p x ζ') / 2 := by
  unfold kerK cavitySq
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp.1 i)]
  have h := two_mul_le_add_sq ‖(ζ - x i)⁻¹‖ ‖(ζ' - x i)⁻¹‖
  have h2 := mul_le_mul_of_nonneg_left h (hp.1 i)
  linarith

/-- `|K(ζ,ζ) - K(ζ',ζ')| ≤ 2 ι⁻³ |ζ - ζ'|` on `Im ≥ ι`. -/
theorem norm_kerK_diag_sub_le (hp : IsCavityWeights p) {ζ ζ' : ℂ} {ι₀ : ℝ} (hι : 0 < ι₀)
    (h : ι₀ ≤ ζ.im) (h' : ι₀ ≤ ζ'.im) :
    ‖kerK p x ζ ζ - kerK p x ζ' ζ'‖ ≤ 2 / ι₀ ^ 3 * ‖ζ - ζ'‖ := by
  unfold kerK
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖(p i : ℂ) * ((ζ - x i)⁻¹ * (ζ - x i)⁻¹) -
        (p i : ℂ) * ((ζ' - x i)⁻¹ * (ζ' - x i)⁻¹)‖
      ≤ ∑ i, p i * (2 / ι₀ ^ 3 * ‖ζ - ζ'‖) := Finset.sum_le_sum fun i _ => ?_
    _ = 2 / ι₀ ^ 3 * ‖ζ - ζ'‖ := by rw [← Finset.sum_mul, hp.2, one_mul]
  have hz := CavityMean.sub_ofReal_ne_zero (hι.trans_le h) (x i)
  have hz' := CavityMean.sub_ofReal_ne_zero (hι.trans_le h') (x i)
  have hα : ‖(ζ - x i)⁻¹‖ ≤ 1 / ι₀ :=
    CavityMean.norm_inv_le_of_im hι (by simpa using h)
  have hβ : ‖(ζ' - x i)⁻¹‖ ≤ 1 / ι₀ :=
    CavityMean.norm_inv_le_of_im hι (by simpa using h')
  have hid : (p i : ℂ) * ((ζ - x i)⁻¹ * (ζ - x i)⁻¹) -
      (p i : ℂ) * ((ζ' - x i)⁻¹ * (ζ' - x i)⁻¹) =
      (p i : ℂ) * ((ζ' - ζ) * (ζ - x i)⁻¹ * (ζ' - x i)⁻¹ * ((ζ - x i)⁻¹ + (ζ' - x i)⁻¹)) := by
    field_simp
    ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp.1 i)]
  refine mul_le_mul_of_nonneg_left ?_ (hp.1 i)
  rw [norm_mul, norm_mul, norm_mul, norm_sub_rev ζ' ζ]
  have hs : ‖(ζ - x i)⁻¹ + (ζ' - x i)⁻¹‖ ≤ 2 / ι₀ := by
    refine (norm_add_le _ _).trans ?_
    have : 2 / ι₀ = 1 / ι₀ + 1 / ι₀ := by ring
    linarith
  have hι3 : 2 / ι₀ ^ 3 = (1 / ι₀) * (1 / ι₀) * (2 / ι₀) := by field_simp
  rw [hι3]
  have h0 : 0 ≤ ‖ζ - ζ'‖ := norm_nonneg _
  calc ‖ζ - ζ'‖ * ‖(ζ - x i)⁻¹‖ * ‖(ζ' - x i)⁻¹‖ * ‖(ζ - x i)⁻¹ + (ζ' - x i)⁻¹‖
      ≤ ‖ζ - ζ'‖ * (1 / ι₀) * (1 / ι₀) * (2 / ι₀) := by gcongr
    _ = 1 / ι₀ * (1 / ι₀) * (2 / ι₀) * ‖ζ - ζ'‖ := by ring

/-- `f'(ζ) = -K(ζ,ζ)` for the finite Stieltjes transform. -/
theorem hasDerivAt_cavityStieltjes {ζ : ℂ} (h : 0 < ζ.im) :
    HasDerivAt (cavityStieltjes p x) (-kerK p x ζ ζ) ζ := by
  have hf : cavityStieltjes p x = fun w : ℂ => ∑ i, (p i : ℂ) * (w - (x i : ℂ))⁻¹ := rfl
  have hk : -kerK p x ζ ζ = ∑ i, -((p i : ℂ) * ((ζ - x i)⁻¹ * (ζ - x i)⁻¹)) := by
    unfold kerK; rw [Finset.sum_neg_distrib]
  rw [hf, hk]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have hne := CavityMean.sub_ofReal_ne_zero h (x i)
  have h1 := (((hasDerivAt_id ζ).sub_const (x i : ℂ)).inv hne).const_mul (p i : ℂ)
  convert h1 using 1
  · funext w; simp only [id, Pi.inv_apply]
  · simp only [id]; field_simp

end Kernel

section Step

/-- `y = -Im a > 0`. -/
def yA (E : ℝ) : ℝ := -(matchedA E).im

/-- `D₀ = 1 - |k| d_*`, `d_* = (1-b)⁻¹`. -/
def dZero (b E : ℝ) : ℝ := 1 - ‖kMinus b E‖ * dStar b

/-- The margin `D₀ - b > 0` of the strict contraction. -/
def gapC (b E : ℝ) : ℝ := dZero b E - b

/-- `m = D₀ - gap/4`, the lower bound of all denominators on the scalar domain. -/
def mC (b E : ℝ) : ℝ := dZero b E - gapC b E / 4

/-- The kernel slope `μ` (`|K| ≤ d_* + μδ₀`). -/
def muC (b E Cs : ℝ) : ℝ := 2 * b * Cs / ((1 - b) ^ 2 * yA E) + 1 / ((1 - b) * yA E)

/-- The product slope `Λ`. -/
def lamC (b E Cs : ℝ) : ℝ :=
  ‖kMinus b E‖ * muC b E Cs + 3 * b ^ 2 * Cs * dStar b + 3 * b ^ 2 * Cs * muC b E Cs

/-- `ι₀ = (1-b) y / 2`, a lower bound for the imaginary parts of `z` and `ζ₀`. -/
def iotaC (b E : ℝ) : ℝ := (1 - b) * yA E / 2

variable {b E : ℝ}

theorem consts_facts (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) :
    0 < yA E ∧ 1 ≤ dStar b ∧ 0 < gapC b E ∧ b < mC b E ∧ mC b E ≤ dZero b E ∧
      b < dZero b E ∧ 0 < iotaC b E := by
  have hEl : |E| < 2 := abs_lt.mpr ⟨hE0, hE1⟩
  have h1b : 0 < 1 - b := by linarith
  have hy0 : 0 < yA E := by
    have := BlockBand.Layers.matchedA_im_neg hEl; unfold yA; linarith
  have hkn := ClockMixingAlg.norm_kMinus_lt hb0 hb1 hE0 hE1
  have hkdS : ‖kMinus b E‖ * dStar b < 1 - b := by
    unfold dStar; rw [mul_one_div, div_lt_iff₀ h1b]; nlinarith
  have hgap : 0 < gapC b E := by unfold gapC dZero; linarith
  refine ⟨hy0, ?_, hgap, ?_, ?_, ?_, ?_⟩
  · unfold dStar; rw [le_div_iff₀ h1b]; linarith
  · unfold mC; unfold gapC at hgap ⊢; linarith
  · unfold mC; linarith
  · unfold gapC at hgap; linarith
  · unfold iotaC; positivity

section Finite

variable {ι : Type} [Fintype ι] {p x : ι → ℝ} {v u : ℂ}

/-- The kernel bounds of Step 3 on the scalar domain. -/
theorem step_kernel (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) {Cs : ℝ}
    (hCs : 0 < Cs) (hp : IsCavityWeights p)
    (hsol : IsCavitySolution p x b (1 - 2 * b) E (boundaryZ b E) v u)
    (hst : ‖v - matchedA E‖ + ‖u - matchedA E‖ ≤
      Cs * ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖)
    (hy : Cs * ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ ≤ yA E / 2) :
    iotaC b E ≤ (-(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * v - (b : ℂ) * u).im ∧
      iotaC b E ≤ (boundaryZ b E).im ∧
      ‖boundaryZ b E - (-(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * v - (b : ℂ) * u)‖ ≤
        Cs * ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ ∧
      ‖kerK p x (-(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * v - (b : ℂ) * u) (boundaryZ b E)‖ ≤
        dStar b + muC b E Cs * ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ ∧
      ‖kerK p x (-(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * v - (b : ℂ) * u)
          (-(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * v - (b : ℂ) * u)‖ ≤
        dStar b + muC b E Cs * ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ := by
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  obtain ⟨hy0, -, -, -, -, -, hι0⟩ := consts_facts hb0 hb1 hE0 hE1
  have h1b : 0 < 1 - b := by linarith
  have hb1' : b ≤ 1 := by linarith
  have hc0 : 0 < 1 - 2 * b := by linarith
  have hc1 : 1 - 2 * b ≤ 1 := by linarith
  generalize hδ : ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ = δ at hst hy ⊢
  have hδ0 : 0 ≤ δ := by rw [← hδ]; exact norm_nonneg _
  generalize ha : matchedA E = a at hst hδ
  generalize hz : boundaryZ b E = z at hst hδ hsol ⊢
  generalize hζ : -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * v - (b : ℂ) * u = ζ₀
  have hyA : yA E = -a.im := by rw [← ha]; rfl
  have hzim : z.im = (1 - b) * yA E := by
    rw [← hz, BlockBand.Layers.boundaryZ_im hE, hyA, ha]; ring
  have hzeq : -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * a - (b : ℂ) * a = z := by
    rw [← hz, BlockBand.Layers.boundaryZ_eq hE, ha]; push_cast; ring
  have hva : ‖v - a‖ ≤ Cs * δ := by linarith [norm_nonneg (u - a)]
  have hua : ‖u - a‖ ≤ Cs * δ := by linarith [norm_nonneg (v - a)]
  have himv : |(v - a).im| ≤ ‖v - a‖ := Complex.abs_im_le_norm _
  have himu : |(u - a).im| ≤ ‖u - a‖ := Complex.abs_im_le_norm _
  have hvim : -v.im = yA E - (v - a).im := by rw [hyA, Complex.sub_im]; ring
  have huim : -u.im = yA E - (u - a).im := by rw [hyA, Complex.sub_im]; ring
  have hvlo : yA E / 2 ≤ -v.im := by
    rw [hvim]; have := (abs_le.mp himv).2; linarith
  have hulo : yA E / 2 ≤ -u.im := by
    rw [huim]; have := (abs_le.mp himu).2; linarith
  have hζ₀im : ζ₀.im = (1 - 2 * b) * (-v.im) + b * (-u.im) := by rw [← hζ]; simp; ring
  have hζ₀lo : iotaC b E ≤ ζ₀.im := by
    rw [hζ₀im]; unfold iotaC
    have h1 : (1 - 2 * b) * (yA E / 2) ≤ (1 - 2 * b) * (-v.im) :=
      mul_le_mul_of_nonneg_left hvlo hc0.le
    have h2 : b * (yA E / 2) ≤ b * (-u.im) := mul_le_mul_of_nonneg_left hulo hb0.le
    linarith
  have hζ₀pos : 0 < ζ₀.im := hι0.trans_le hζ₀lo
  have hzlo : iotaC b E ≤ z.im := by
    rw [hzim]; unfold iotaC
    have : 0 ≤ (1 - b) * yA E := by positivity
    linarith
  have hv : v = cavityStieltjes p x ζ₀ := by rw [← hζ, ← hz] at *; exact hsol.1
  have hzζ : ‖z - ζ₀‖ ≤ Cs * δ := by
    have hI3 : z - ζ₀ = ((1 - 2 * b : ℝ) : ℂ) * (v - a) + (b : ℂ) * (u - a) := by
      rw [← hzeq, ← hζ]; ring
    rw [hI3]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hc0.le,
      Real.norm_of_nonneg hb0.le]
    have h1 : (1 - 2 * b) * ‖v - a‖ ≤ ‖v - a‖ := mul_le_of_le_one_left (norm_nonneg _) hc1
    have h2 : b * ‖u - a‖ ≤ ‖u - a‖ := mul_le_of_le_one_left (norm_nonneg _) hb1'
    linarith
  -- the imaginary identity at `ζ₀`
  have hS₀eq : -v.im = ζ₀.im * cavitySq p x ζ₀ := by
    have := CavityMean.im_cavityStieltjes p x ζ₀
    rw [← hv] at this; rw [this]; ring
  have hμ1 : 0 ≤ 2 * b * Cs / ((1 - b) ^ 2 * yA E) := by positivity
  have hμ2 : 0 ≤ 1 / ((1 - b) * yA E) := by positivity
  have hS₀le : cavitySq p x ζ₀ ≤ dStar b + muC b E Cs * δ := by
    have hdiff : (-v.im) - (-u.im) ≤ Cs * δ := by
      rw [hvim, huim]
      have h1 := (abs_le.mp himv).1; have h2 := (abs_le.mp himu).2
      linarith
    set S₀ := cavitySq p x ζ₀
    set w : ℝ := 2 * b * Cs / ((1 - b) ^ 2 * yA E) with hw
    have hfac : (1 - b) * w * iotaC b E = b * Cs := by
      rw [hw]; unfold iotaC; field_simp
    have hmono : (1 - b) * w * δ * iotaC b E ≤ (1 - b) * w * δ * ζ₀.im :=
      mul_le_mul_of_nonneg_left hζ₀lo (by positivity)
    have hbc : b * Cs * δ = (1 - b) * w * δ * iotaC b E := by rw [← hfac]; ring
    have hbd : b * ((-v.im) - (-u.im)) ≤ b * (Cs * δ) := mul_le_mul_of_nonneg_left hdiff hb0.le
    -- `(1-b) ζ₀.im S₀ ≤ ζ₀.im + (1-b) w δ ζ₀.im`
    have hkey : (1 - b) * (ζ₀.im * S₀) ≤ ζ₀.im + (1 - b) * w * δ * ζ₀.im := by
      rw [← hS₀eq, hζ₀im] at *
      nlinarith
    have h3 : ((1 - b) * ζ₀.im) * S₀ ≤ ((1 - b) * ζ₀.im) * (dStar b + w * δ) := by
      have : (1 - b) * ζ₀.im * dStar b = ζ₀.im := by unfold dStar; field_simp
      have e : ((1 - b) * ζ₀.im) * (dStar b + w * δ) = ζ₀.im + (1 - b) * w * δ * ζ₀.im := by
        rw [mul_add, this]; ring
      rw [e]; linarith
    have h4 := le_of_mul_le_mul_left h3 (by positivity)
    have : w * δ ≤ muC b E Cs * δ := by
      refine mul_le_mul_of_nonneg_right ?_ hδ0
      unfold muC; rw [← hw]; linarith
    linarith
  have hSzle : cavitySq p x z ≤ dStar b + muC b E Cs * δ := by
    have hfz := CavityMean.im_cavityStieltjes p x z
    have hfa : -(cavityStieltjes p x z).im ≤ yA E + δ := by
      have h1 : |(cavityStieltjes p x z - a).im| ≤ δ := by
        rw [← hδ]; exact Complex.abs_im_le_norm _
      have h2 : -(cavityStieltjes p x z).im = yA E - (cavityStieltjes p x z - a).im := by
        rw [hyA, Complex.sub_im]; ring
      rw [h2]; have := (abs_le.mp h1).1; linarith
    have hS : z.im * cavitySq p x z ≤ yA E + δ := by linarith
    rw [hzim] at hS
    have h3 : ((1 - b) * yA E) * cavitySq p x z ≤
        ((1 - b) * yA E) * (dStar b + (1 / ((1 - b) * yA E)) * δ) := by
      have : ((1 - b) * yA E) * (dStar b + (1 / ((1 - b) * yA E)) * δ) = yA E + δ := by
        unfold dStar; field_simp
      rw [this]; linarith
    have h4 := le_of_mul_le_mul_left h3 (by positivity)
    have : (1 / ((1 - b) * yA E)) * δ ≤ muC b E Cs * δ := by
      refine mul_le_mul_of_nonneg_right ?_ hδ0
      unfold muC; linarith
    linarith
  refine ⟨hζ₀lo, hzlo, hzζ, ?_, (norm_kerK_self_le hp ζ₀).trans hS₀le⟩
  exact (norm_kerK_le hp ζ₀ z).trans (by linarith)

/-- Denominators on the scalar domain: `|K| ≤ d_* + μδ`, `|w| ≤ |k| + 3b²C_sδ`,
`4Λδ ≤ gap`, `δ ≤ 1` give `|1 - Kw| ≥ m`. -/
theorem den_lower {Cs δ : ℝ} (hCs : 0 < Cs) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hΛ : 4 * lamC b E Cs * δ ≤ gapC b E) (hμ : 0 ≤ muC b E Cs)
    (hdS : 0 ≤ dStar b) {K' w : ℂ}
    (hK' : ‖K'‖ ≤ dStar b + muC b E Cs * δ) (hw : ‖w‖ ≤ ‖kMinus b E‖ + 3 * b ^ 2 * Cs * δ) :
    mC b E ≤ ‖1 - K' * w‖ := by
  have h1 : ‖K'‖ * ‖w‖ ≤ (dStar b + muC b E Cs * δ) * (‖kMinus b E‖ + 3 * b ^ 2 * Cs * δ) :=
    mul_le_mul hK' hw (norm_nonneg _) (by positivity)
  have hδ2 : δ * δ ≤ δ := by nlinarith
  have h2 : (dStar b + muC b E Cs * δ) * (‖kMinus b E‖ + 3 * b ^ 2 * Cs * δ) ≤
      ‖kMinus b E‖ * dStar b + lamC b E Cs * δ := by
    have e : (dStar b + muC b E Cs * δ) * (‖kMinus b E‖ + 3 * b ^ 2 * Cs * δ) =
        ‖kMinus b E‖ * dStar b + (‖kMinus b E‖ * muC b E Cs + 3 * b ^ 2 * Cs * dStar b) * δ +
          3 * b ^ 2 * Cs * muC b E Cs * (δ * δ) := by ring
    have : 3 * b ^ 2 * Cs * muC b E Cs * (δ * δ) ≤ 3 * b ^ 2 * Cs * muC b E Cs * δ :=
      mul_le_mul_of_nonneg_left hδ2 (by positivity)
    rw [e]; unfold lamC
    linarith
  have h3 : ‖(1 : ℂ)‖ - ‖K' * w‖ ≤ ‖1 - K' * w‖ := norm_sub_norm_le _ _
  rw [norm_one, norm_mul] at h3
  unfold mC gapC dZero at *
  linarith

/-- The algebra of Steps 3–4: `u' - s = [Φ(u,t) - F(t)] + [F(t) - F(s)]` with `t = -K`,
`D₁ = 1 + (c + b²u²)t`, `D₂ = 1 + kt`, `D₃ = 1 + ks` and `s = F(s)`. -/
theorem jet_identity {a u K s c b k D1 D2 D3 : ℂ} (hk : k = c + b ^ 2 * a ^ 2)
    (hD1 : D1 = 1 - K * (c + b ^ 2 * u * u)) (hD2 : D2 = 1 - K * k) (hD3 : D3 = 1 + k * s)
    (h1 : D1 ≠ 0) (h2 : D2 ≠ 0) (h3 : D3 ≠ 0) (hs : s * D3 = -(a ^ 2 * (1 + c * s))) :
    -(1 - b * (-(K * b * u * u) / D1)) * u ^ 2 - s =
      (1 - c * K) ^ 2 * (a ^ 2 - u ^ 2) / (D1 * D2) + a ^ 4 * b ^ 2 * (-K - s) / (D2 * D3) := by
  have hs' : s = -(a ^ 2 * (1 + c * s)) / D3 := by rw [eq_div_iff h3]; exact hs
  conv_lhs => rw [hs']
  field_simp
  rw [hD1, hD2, hD3, hk]
  ring

/-- **Steps 2–4 for a finite law** from the stability bound, on the scalar domain. -/
theorem step_scalar_jet (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) {Cs : ℝ}
    (hCs : 0 < Cs) (hp : IsCavityWeights p)
    (hsol : IsCavitySolution p x b (1 - 2 * b) E (boundaryZ b E) v u)
    (hst : ‖v - matchedA E‖ + ‖u - matchedA E‖ ≤
      Cs * ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖)
    (hδ1 : ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ ≤ 1)
    (hCsδ1 : Cs * ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ ≤ 1)
    (hy : Cs * ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ ≤ yA E / 2)
    (hΛ : 4 * lamC b E Cs * ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ ≤ gapC b E)
    (hbC : 4 * b * Cs * ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ ≤ gapC b E)
    (hμδ : muC b E Cs * ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ ≤ 1) :
    ‖u - matchedA E‖ ≤ (b + gapC b E / 4) / mC b E *
        ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ ∧
      ∀ s : ℂ, IsStationaryJet b E s →
        ‖-(1 - (b : ℂ) * vDeriv p x b (1 - 2 * b) E v u) * u ^ 2 - s‖ ≤
          b ^ 2 / (mC b E * dZero b E) * ‖-kerK p x (boundaryZ b E) (boundaryZ b E) - s‖ +
            (3 * (2 + dStar b) ^ 2 * Cs / mC b E ^ 2 + 2 * Cs / iotaC b E ^ 3) *
              ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ := by
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  obtain ⟨hy0, hdS1, hgap, hmb, hmD, hD₀b, hι0⟩ := consts_facts hb0 hb1 hE0 hE1
  obtain ⟨hζlo, hzlo, hzζ, hKle, hK₀le⟩ := step_kernel hb0 hb1 hE0 hE1 hCs hp hsol hst hy
  have hm0 : 0 < mC b E := hb0.trans hmb
  have hc0 : 0 < 1 - 2 * b := by linarith
  have hc1 : 1 - 2 * b ≤ 1 := by linarith
  have hμ0 : 0 ≤ muC b E Cs := by
    unfold muC
    have h1b : 0 < 1 - b := by linarith
    positivity
  have hdS0 : 0 ≤ dStar b := by linarith
  have hkc : kMinus b E = ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2 := rfl
  have ha1 : ‖matchedA E‖ = 1 := BlockBand.Layers.norm_matchedA hE
  have ha0 : matchedA E ≠ 0 := by intro h0; rw [h0, norm_zero] at ha1; exact zero_ne_one ha1
  have hzeq : -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E - (b : ℂ) * matchedA E =
      boundaryZ b E := by
    rw [BlockBand.Layers.boundaryZ_eq hE]; push_cast; ring
  have hza' : boundaryZ b E - (b : ℂ) * matchedA E = (matchedA E)⁻¹ := by
    unfold boundaryZ; ring
  have hzpos : 0 < (boundaryZ b E).im := hι0.trans_le hzlo
  generalize hδ : ‖cavityStieltjes p x (boundaryZ b E) - matchedA E‖ = δ at *
  have hδ0 : 0 ≤ δ := by rw [← hδ]; exact norm_nonneg _
  generalize hk : kMinus b E = k at *
  generalize ha : matchedA E = a at *
  generalize hz : boundaryZ b E = z at *
  generalize hζ : -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * v - (b : ℂ) * u = ζ₀ at *
  have haz : a * (z - (b : ℂ) * a) = 1 := by rw [hza']; exact mul_inv_cancel₀ ha0
  have hva : ‖v - a‖ ≤ Cs * δ := by linarith [norm_nonneg (u - a)]
  have hua : ‖u - a‖ ≤ Cs * δ := by linarith [norm_nonneg (v - a)]
  have hζ₀pos : 0 < ζ₀.im := hι0.trans_le hζlo
  have hv : v = cavityStieltjes p x ζ₀ := by rw [← hζ]; exact hsol.1
  have hu : u * (z - (b : ℂ) * v) = 1 := by
    have hne : z - (b : ℂ) * v ≠ 0 :=
      CavityMean.ne_zero_of_im_pos (hzpos.trans_le (port_den_im hb0.le hsol.2.2.1.le))
    rw [hsol.2.1]; exact inv_mul_cancel₀ hne
  have hI1 : u - a = a * b * u * (v - a) := by linear_combination a * hu - u * haz
  have hI2 : v - cavityStieltjes p x z = kerK p x ζ₀ z * (z - ζ₀) := by
    rw [hv]; exact stieltjes_sub_eq hζ₀pos hzpos
  have hI3 : z - ζ₀ = ((1 - 2 * b : ℝ) : ℂ) * (v - a) + (b : ℂ) * (u - a) := by
    rw [← hzeq, ← hζ]; ring
  have hupa : ‖u + a‖ ≤ 3 := by
    have : u + a = (u - a) + 2 * a := by ring
    rw [this]; refine (norm_add_le _ _).trans ?_
    rw [norm_mul, ha1]; norm_num; linarith
  have hu1 : ‖u‖ ≤ 1 + Cs * δ := by
    have : u = (u - a) + a := by ring
    rw [this]; refine (norm_add_le _ _).trans ?_; rw [ha1]; linarith
  have hb2 : 0 ≤ b ^ 2 * (Cs * δ) := by positivity
  have hcoef : ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * a * u‖ ≤ ‖k‖ + 3 * b ^ 2 * Cs * δ := by
    have : ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * a * u = k + (b : ℂ) ^ 2 * a * (u - a) := by
      rw [hkc]; ring
    rw [this]; refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hb0.le, ha1,
      mul_one]
    have : b ^ 2 * ‖u - a‖ ≤ b ^ 2 * (Cs * δ) := mul_le_mul_of_nonneg_left hua (by positivity)
    linarith
  have hcoef2 : ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * u * u‖ ≤ ‖k‖ + 3 * b ^ 2 * Cs * δ := by
    have : ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * u * u = k + (b : ℂ) ^ 2 * ((u - a) * (u + a)) := by
      rw [hkc]; ring
    rw [this]; refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have h1 : ‖u - a‖ * ‖u + a‖ ≤ Cs * δ * 3 :=
      mul_le_mul hua hupa (norm_nonneg _) (by positivity)
    have : b ^ 2 * (‖u - a‖ * ‖u + a‖) ≤ b ^ 2 * (Cs * δ * 3) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hden : ∀ K' w : ℂ, ‖K'‖ ≤ dStar b + muC b E Cs * δ → ‖w‖ ≤ ‖k‖ + 3 * b ^ 2 * Cs * δ →
      mC b E ≤ ‖1 - K' * w‖ := by
    intro K' w hK' hw
    rw [← hk] at hw
    exact den_lower hCs hδ0 hδ1 hΛ hμ0 hdS0 hK' hw
  -- Step 2
  have hQ := hden _ _ hKle hcoef
  have hδv : (v - a) * (1 - kerK p x ζ₀ z * (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * a * u)) =
      cavityStieltjes p x z - a := by
    linear_combination hI2 + kerK p x ζ₀ z * hI3 + kerK p x ζ₀ z * (b : ℂ) * hI1
  have hva' : ‖v - a‖ ≤ δ / mC b E := by
    rw [le_div_iff₀ hm0, ← hδ]
    calc ‖v - a‖ * mC b E ≤ ‖v - a‖ *
          ‖1 - kerK p x ζ₀ z * (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * a * u)‖ :=
          mul_le_mul_of_nonneg_left hQ (norm_nonneg _)
      _ = ‖cavityStieltjes p x z - a‖ := by rw [← norm_mul, hδv]
  refine ⟨?_, ?_⟩
  · rw [hI1, norm_mul, norm_mul, norm_mul, ha1, Complex.norm_real, Real.norm_of_nonneg hb0.le,
      one_mul]
    have h1 : b * ‖u‖ ≤ b + gapC b E / 4 := by
      have : b * ‖u‖ ≤ b * (1 + Cs * δ) := mul_le_mul_of_nonneg_left hu1 hb0.le
      nlinarith
    calc b * ‖u‖ * ‖v - a‖ ≤ (b + gapC b E / 4) * (δ / mC b E) :=
          mul_le_mul h1 hva' (norm_nonneg _) (by linarith)
      _ = (b + gapC b E / 4) / mC b E * δ := by ring
  -- Steps 3–4
  intro s hs
  have hsn : ‖s‖ ≤ dStar b := hs.2
  have hs1 := hs.1
  rw [hk, ha] at hs1
  set K₀ := kerK p x ζ₀ ζ₀ with hK₀
  have hDen1 := hden K₀ (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * u * u) hK₀le hcoef2
  have hDa := hden K₀ k hK₀le (by linarith [mul_nonneg (mul_nonneg (sq_nonneg b) hCs.le) hδ0])
  have hDs : dZero b E ≤ ‖1 + k * s‖ := by
    have h2 : ‖(1 : ℂ)‖ - ‖-(k * s)‖ ≤ ‖1 - -(k * s)‖ := norm_sub_norm_le _ _
    rw [norm_one, norm_neg, norm_mul, sub_neg_eq_add] at h2
    have : ‖k‖ * ‖s‖ ≤ ‖k‖ * dStar b := mul_le_mul_of_nonneg_left hsn (norm_nonneg _)
    unfold dZero; rw [hk]; linarith
  have hDsm : mC b E ≤ ‖1 + k * s‖ := hmD.trans hDs
  have hDen1ne : 1 - K₀ * (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * u * u) ≠ 0 :=
    norm_pos_iff.mp (hm0.trans_le hDen1)
  have hDane : 1 - K₀ * k ≠ 0 := norm_pos_iff.mp (hm0.trans_le hDa)
  have hDsne : 1 + k * s ≠ 0 := norm_pos_iff.mp (hm0.trans_le hDsm)
  have hvD : vDeriv p x b (1 - 2 * b) E v u =
      -(K₀ * b * u * u) / (1 - K₀ * (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * u * u)) := by
    unfold vDeriv; rw [hζ]
  have hsF : s * (1 + k * s) = -(a ^ 2 * (1 + ((1 - 2 * b : ℝ) : ℂ) * s)) := by
    linear_combination hs1
  have hsplit : -(1 - (b : ℂ) * vDeriv p x b (1 - 2 * b) E v u) * u ^ 2 - s =
      (1 - ((1 - 2 * b : ℝ) : ℂ) * K₀) ^ 2 * (a ^ 2 - u ^ 2) /
          ((1 - K₀ * (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * u * u)) * (1 - K₀ * k)) +
        a ^ 4 * (b : ℂ) ^ 2 * (-K₀ - s) / ((1 - K₀ * k) * (1 + k * s)) := by
    rw [hvD]
    exact jet_identity hkc rfl rfl rfl hDen1ne hDane hDsne hsF
  have hK₀1 : ‖K₀‖ ≤ dStar b + 1 := by linarith
  have hcK : ‖1 - ((1 - 2 * b : ℝ) : ℂ) * K₀‖ ≤ 2 + dStar b := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le]
    have : (1 - 2 * b) * ‖K₀‖ ≤ ‖K₀‖ := mul_le_of_le_one_left (norm_nonneg _) hc1
    linarith
  have hau : ‖a ^ 2 - u ^ 2‖ ≤ 3 * (Cs * δ) := by
    have : a ^ 2 - u ^ 2 = -((u - a) * (u + a)) := by ring
    rw [this, norm_neg, norm_mul]
    have := mul_le_mul hua hupa (norm_nonneg _) (by positivity)
    linarith
  have hT1 : ‖(1 - ((1 - 2 * b : ℝ) : ℂ) * K₀) ^ 2 * (a ^ 2 - u ^ 2) /
      ((1 - K₀ * (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * u * u)) * (1 - K₀ * k))‖ ≤
      3 * (2 + dStar b) ^ 2 * Cs / mC b E ^ 2 * δ := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, div_le_iff₀ (by
      exact mul_pos (hm0.trans_le hDen1) (hm0.trans_le hDa))]
    have hn : ‖1 - ((1 - 2 * b : ℝ) : ℂ) * K₀‖ ^ 2 * ‖a ^ 2 - u ^ 2‖ ≤
        (2 + dStar b) ^ 2 * (3 * (Cs * δ)) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hcK 2) hau (norm_nonneg _) (by positivity)
    have hd : mC b E ^ 2 ≤ ‖1 - K₀ * (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * u * u)‖ *
        ‖1 - K₀ * k‖ := by
      rw [sq]; exact mul_le_mul hDen1 hDa hm0.le (norm_nonneg _)
    have hc' : 0 ≤ 3 * (2 + dStar b) ^ 2 * Cs / mC b E ^ 2 * δ := by positivity
    calc ‖1 - ((1 - 2 * b : ℝ) : ℂ) * K₀‖ ^ 2 * ‖a ^ 2 - u ^ 2‖
        ≤ (2 + dStar b) ^ 2 * (3 * (Cs * δ)) := hn
      _ = 3 * (2 + dStar b) ^ 2 * Cs / mC b E ^ 2 * δ * mC b E ^ 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hd hc'
  have hts : ‖-K₀ - s‖ ≤ ‖-kerK p x z z - s‖ + 2 / iotaC b E ^ 3 * (Cs * δ) := by
    have : -K₀ - s = (-kerK p x z z - s) + (kerK p x z z - K₀) := by ring
    rw [this]; refine (norm_add_le _ _).trans ?_
    have h := norm_kerK_diag_sub_le (x := x) hp hι0 hzlo hζlo
    have : 2 / iotaC b E ^ 3 * ‖z - ζ₀‖ ≤ 2 / iotaC b E ^ 3 * (Cs * δ) :=
      mul_le_mul_of_nonneg_left hzζ (by positivity)
    linarith
  have hT2 : ‖a ^ 4 * (b : ℂ) ^ 2 * (-K₀ - s) / ((1 - K₀ * k) * (1 + k * s))‖ ≤
      b ^ 2 / (mC b E * dZero b E) * ‖-K₀ - s‖ := by
    have hpos : 0 < ‖1 - K₀ * k‖ * ‖1 + k * s‖ :=
      mul_pos (hm0.trans_le hDa) (hm0.trans_le hDsm)
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, ha1, one_pow, one_mul,
      Complex.norm_real, Real.norm_of_nonneg hb0.le, div_le_iff₀ hpos]
    have hd : mC b E * dZero b E ≤ ‖1 - K₀ * k‖ * ‖1 + k * s‖ :=
      mul_le_mul hDa hDs (by linarith) (norm_nonneg _)
    have e : b ^ 2 / (mC b E * dZero b E) * ‖-K₀ - s‖ * (mC b E * dZero b E) =
        b ^ 2 * ‖-K₀ - s‖ := by
      have : mC b E * dZero b E ≠ 0 := (mul_pos hm0 (hm0.trans_le hmD)).ne'
      rw [mul_right_comm, div_mul_cancel₀ _ this]
    calc b ^ 2 * ‖-K₀ - s‖ = b ^ 2 / (mC b E * dZero b E) * ‖-K₀ - s‖ * (mC b E * dZero b E) :=
          e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by
          have : 0 < mC b E * dZero b E := mul_pos hm0 (hm0.trans_le hmD)
          positivity)
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hq₁0 : 0 ≤ b ^ 2 / (mC b E * dZero b E) := by
    have : 0 < mC b E * dZero b E := mul_pos hm0 (hm0.trans_le hmD)
    positivity
  have hq₁1 : b ^ 2 / (mC b E * dZero b E) ≤ 1 := by
    have h0 : 0 < mC b E * dZero b E := mul_pos hm0 (hm0.trans_le hmD)
    rw [div_le_one h0]
    have : b * b ≤ mC b E * dZero b E := mul_le_mul hmb.le hD₀b.le hb0.le hm0.le
    rw [sq]; exact this
  have h4 : b ^ 2 / (mC b E * dZero b E) * ‖-K₀ - s‖ ≤
      b ^ 2 / (mC b E * dZero b E) * ‖-kerK p x z z - s‖ +
        b ^ 2 / (mC b E * dZero b E) * (2 / iotaC b E ^ 3 * (Cs * δ)) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hts hq₁0
  have h5 : b ^ 2 / (mC b E * dZero b E) * (2 / iotaC b E ^ 3 * (Cs * δ)) ≤
      2 * Cs / iotaC b E ^ 3 * δ := by
    have : b ^ 2 / (mC b E * dZero b E) * (2 / iotaC b E ^ 3 * (Cs * δ)) ≤
        1 * (2 / iotaC b E ^ 3 * (Cs * δ)) := mul_le_mul_of_nonneg_right hq₁1 (by positivity)
    have e : 2 / iotaC b E ^ 3 * (Cs * δ) = 2 * Cs / iotaC b E ^ 3 * δ := by ring
    linarith
  have e : (3 * (2 + dStar b) ^ 2 * Cs / mC b E ^ 2 + 2 * Cs / iotaC b E ^ 3) * δ =
      3 * (2 + dStar b) ^ 2 * Cs / mC b E ^ 2 * δ + 2 * Cs / iotaC b E ^ 3 * δ := by ring
  rw [e]
  linarith only [hT1, hT2, h4, h5]

end Finite

end Step

section Matrix

variable {b E : ℝ}

/-- `δ₀(X) = |f(z) - a|` with `f(ζ) = W⁻¹ Tr(ζ - X)⁻¹`. -/
theorem jetDistance0_eq {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) :
    jetDistance0 b E X = ‖normalizedResolventTrace X (boundaryZ b E) - matchedA E‖ := rfl

/-- `δ₁(X) = |f'(z) - s|`. -/
theorem jetDistance1_eq {W : ℕ} (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    jetDistance1 b E s X = ‖deriv (normalizedResolventTrace X) (boundaryZ b E) - s‖ := rfl

/-- For Hermitian `X`, `f'(ζ) = -Σ_i W⁻¹ (ζ - λ_i)⁻²` on the upper half-plane. -/
theorem hasDerivAt_normalizedResolventTrace {W : ℕ} {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) {ζ : ℂ} (hζ : 0 < ζ.im) :
    HasDerivAt (normalizedResolventTrace X)
      (-kerK (fun _ : Fin W => (W : ℝ)⁻¹) hX.eigenvalues ζ ζ) ζ := by
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : cavityStieltjes (fun _ : Fin W => (W : ℝ)⁻¹) hX.eigenvalues =ᶠ[𝓝 ζ]
      normalizedResolventTrace X := by
    filter_upwards [hopen.mem_nhds hζ] with w hw
    exact (normalizedResolventTrace_eq hX hw.ne').symm
  exact (hasDerivAt_cavityStieltjes hζ).congr_of_eventuallyEq hev.symm

/-- `u'(z) = -(1 - b v'(z)) u(z)²` for the matrix cavity solution. -/
theorem deriv_cavityU_eq {W : ℕ} (hW : 0 < W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) (hb0 : 0 < b) (hb1 : b < 1 / 2) {z : ℂ} (hz : 0 < z.im) :
    deriv (cavityU X b E) z =
      -(1 - (b : ℂ) * vDeriv (fun _ : Fin W => (W : ℝ)⁻¹) hX.eigenvalues b (1 - 2 * b) E
          (cavityV X b E z) (cavityU X b E z)) * cavityU X b E z ^ 2 := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hs : ∀ w : ℂ, 0 < w.im → IsCavitySolution (fun _ => (W : ℝ)⁻¹) hX.eigenvalues b
      (1 - 2 * b) E w (cavitySol X b E w).1 (cavitySol X b E w).2 := fun w hw =>
    (isCavityMatrixSolution_iff hX hb0 hc).mp (cavitySol_spec hW hX hb0 hb1 E hw)
  have hv := cavitySol_hasDerivAt_v (isCavityWeights_uniform hW) hb0 hc hs hz
  have hne : z - (b : ℂ) * (cavitySol X b E z).1 ≠ 0 :=
    CavityMean.ne_zero_of_im_pos (hz.trans_le (port_den_im hb0.le (hs z hz).2.2.1.le))
  have hd := ((hasDerivAt_id z).sub (hv.const_mul (b : ℂ))).inv hne
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : (fun w => (w - (b : ℂ) * (cavitySol X b E w).1)⁻¹) =ᶠ[𝓝 z] cavityU X b E := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact ((hs w hw).2.1).symm
  rw [(hd.congr_of_eventuallyEq hev.symm).deriv]
  have hu : (z - (b : ℂ) * (cavitySol X b E z).1)⁻¹ = cavityU X b E z := ((hs z hz).2.1).symm
  have hid : ((id : ℂ → ℂ) - fun y => (b : ℂ) * (cavitySol X b E y).1) z =
      z - (b : ℂ) * (cavitySol X b E z).1 := rfl
  rw [hid, div_eq_mul_inv, ← inv_pow, hu]
  rfl

/-- **The deterministic one-step bounds of the open-inputs lemma**:
there are `r₀ > 0`, `q < 1`, `C` (depending on `b, E`) such that for every `W ≥ 1` and every
Hermitian `X` with `δ₀(X) ≤ r₀`, the cavity solution satisfies `|u(z) - a| ≤ q δ₀(X)` and
`|u'(z) - s| ≤ q δ₁(X) + C δ₀(X)` at every stationary jet `s`. -/
theorem step_bound (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) :
    ∃ r₀ q C : ℝ, 0 < r₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧
      ∀ {W : ℕ}, 0 < W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
        jetDistance0 b E X ≤ r₀ →
        ‖cavityU X b E (boundaryZ b E) - matchedA E‖ ≤ q * jetDistance0 b E X ∧
        ∀ s : ℂ, IsStationaryJet b E s →
          ‖deriv (cavityU X b E) (boundaryZ b E) - s‖ ≤
            q * jetDistance1 b E s X + C * jetDistance0 b E X := by
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  obtain ⟨hy0, hdS1, hgap, hmb, hmD, hD₀b, hι0⟩ := consts_facts hb0 hb1 hE0 hE1
  have hc : 0 < 1 - 2 * b := by linarith
  have h1b : 0 < 1 - b := by linarith
  have hm0 : 0 < mC b E := hb0.trans hmb
  have hzim : (boundaryZ b E).im = (1 - b) * yA E := by
    rw [BlockBand.Layers.boundaryZ_im hE]; unfold yA; ring
  have hzpos : 0 < (boundaryZ b E).im := by rw [hzim]; positivity
  have ha1 : ‖matchedA E‖ = 1 := BlockBand.Layers.norm_matchedA hE
  have hzeq : -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E - (b : ℂ) * matchedA E =
      boundaryZ b E := by
    rw [BlockBand.Layers.boundaryZ_eq hE]; push_cast; ring
  have hza' : boundaryZ b E - (b : ℂ) * matchedA E = (matchedA E)⁻¹ := by
    unfold boundaryZ; ring
  obtain ⟨Cs, hCs, hstab⟩ := cavity_stability (b := b) (c := 1 - 2 * b) (η := (boundaryZ b E).im)
    (M := ‖boundaryZ b E‖) (astar := 1) hb0 hc hzpos (norm_nonneg _) one_pos
  have hμ0 : 0 ≤ muC b E Cs := by unfold muC; positivity
  have hΛ0 : 0 ≤ lamC b E Cs := by
    unfold lamC; have : 0 ≤ dStar b := by linarith
    positivity
  set r₀ : ℝ := min (min 1 (1 / Cs)) (min (yA E / (2 * Cs))
    (min (gapC b E / (4 * lamC b E Cs + 1)) (min (gapC b E / (4 * b * Cs + 1))
      (1 / (muC b E Cs + 1))))) with hr₀
  have hqs0 : 0 ≤ (b + gapC b E / 4) / mC b E := by
    have : 0 ≤ b + gapC b E / 4 := by linarith
    positivity
  have hqs1 : (b + gapC b E / 4) / mC b E < 1 := by
    rw [div_lt_one hm0]; unfold mC; unfold gapC at hgap ⊢; linarith
  have hD0 : 0 < dZero b E := hm0.trans_le hmD
  have hq₁0 : 0 ≤ b ^ 2 / (mC b E * dZero b E) := by positivity
  have hq₁1 : b ^ 2 / (mC b E * dZero b E) < 1 := by
    rw [div_lt_one (mul_pos hm0 hD0)]
    have : b * b < mC b E * dZero b E := mul_lt_mul'' hmb hD₀b hb0.le hb0.le
    rw [sq]; exact this
  refine ⟨r₀, max ((b + gapC b E / 4) / mC b E) (b ^ 2 / (mC b E * dZero b E)),
    3 * (2 + dStar b) ^ 2 * Cs / mC b E ^ 2 + 2 * Cs / iotaC b E ^ 3, ?_,
    le_max_of_le_left hqs0, max_lt hqs1 hq₁1, by positivity, ?_⟩
  · rw [hr₀]
    refine lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  intro W hW X hX hδ
  set p : Fin W → ℝ := fun _ => (W : ℝ)⁻¹ with hpdef
  have hp : IsCavityWeights p := isCavityWeights_uniform hW
  have hfX : normalizedResolventTrace X (boundaryZ b E) =
      cavityStieltjes p hX.eigenvalues (boundaryZ b E) := normalizedResolventTrace_eq hX hzpos.ne'
  have hδeq : jetDistance0 b E X = ‖cavityStieltjes p hX.eigenvalues (boundaryZ b E) - matchedA E‖ := by
    rw [jetDistance0_eq, hfX]
  have hsol : IsCavitySolution p hX.eigenvalues b (1 - 2 * b) E (boundaryZ b E)
      (cavityV X b E (boundaryZ b E)) (cavityU X b E (boundaryZ b E)) :=
    (isCavityMatrixSolution_iff hX hb0 hc).mp (cavitySol_spec hW hX hb0 hb1 E hzpos)
  rw [hδeq] at hδ ⊢
  generalize hδg : ‖cavityStieltjes p hX.eigenvalues (boundaryZ b E) - matchedA E‖ = δ at hδ
  have hδ0 : 0 ≤ δ := by rw [← hδg]; exact norm_nonneg _
  have hst : ‖cavityV X b E (boundaryZ b E) - matchedA E‖ +
      ‖cavityU X b E (boundaryZ b E) - matchedA E‖ ≤ Cs * δ := by
    have h := hstab (Fin W) p hX.eigenvalues E (boundaryZ b E) _ _ (matchedA E) (matchedA E) δ hp
      le_rfl le_rfl hsol ?_ ?_ ?_ ?_ ?_
    · rw [norm_sub_rev (cavityV _ _ _ _), norm_sub_rev (cavityU _ _ _ _)]; exact h
    · have := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩); linarith
    · rw [ha1]
    · rw [ha1, hzim]; unfold yA
      have := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩)
      nlinarith
    · rw [hzeq, norm_sub_rev, hδg]
    · rw [hza', inv_inv, sub_self, norm_zero]; exact hδ0
  have hδ1 : δ ≤ 1 := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδCs : δ ≤ 1 / Cs := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hCsδ1 : Cs * δ ≤ 1 := by
    rw [le_div_iff₀ hCs] at hδCs; linarith
  have hδy : δ ≤ yA E / (2 * Cs) := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hCsδy : Cs * δ ≤ yA E / 2 := by
    rw [le_div_iff₀ (by positivity)] at hδy; linarith
  have hδΛ : δ ≤ gapC b E / (4 * lamC b E Cs + 1) :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hΛδ : 4 * lamC b E Cs * δ ≤ gapC b E := by
    rw [le_div_iff₀ (by positivity)] at hδΛ
    linarith [show δ * (4 * lamC b E Cs + 1) = 4 * lamC b E Cs * δ + δ by ring]
  have hδb : δ ≤ gapC b E / (4 * b * Cs + 1) := hδ.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hbCsδ : 4 * b * Cs * δ ≤ gapC b E := by
    rw [le_div_iff₀ (by positivity)] at hδb
    linarith [show δ * (4 * b * Cs + 1) = 4 * b * Cs * δ + δ by ring]
  have hδμ : δ ≤ 1 / (muC b E Cs + 1) := hδ.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hμδ : muC b E Cs * δ ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hδμ
    linarith [show δ * (muC b E Cs + 1) = muC b E Cs * δ + δ by ring]
  rw [← hδg] at hst hδ1 hCsδ1 hCsδy hΛδ hbCsδ hμδ
  obtain ⟨hsc, hjet⟩ := step_scalar_jet hb0 hb1 hE0 hE1 hCs hp hsol hst hδ1 hCsδ1 hCsδy hΛδ
    hbCsδ hμδ
  rw [hδg] at hsc hjet
  refine ⟨hsc.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0), ?_⟩
  intro s hs
  have hd1 : jetDistance1 b E s X = ‖-kerK p hX.eigenvalues (boundaryZ b E) (boundaryZ b E) - s‖ := by
    rw [jetDistance1_eq, (hasDerivAt_normalizedResolventTrace hX hzpos).deriv]
  rw [hd1, deriv_cavityU_eq hW hX hb0 hb1 hzpos]
  refine (hjet s hs).trans ?_
  have := mul_le_mul_of_nonneg_right (le_max_right ((b + gapC b E / 4) / mC b E)
    (b ^ 2 / (mC b E * dZero b E))) (norm_nonneg (-kerK p hX.eigenvalues (boundaryZ b E)
      (boundaryZ b E) - s))
  linarith

end Matrix

end OpenInputsProof

end BlockBand.Endpoints.Clock
