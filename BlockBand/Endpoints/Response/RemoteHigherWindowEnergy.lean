module

public import BlockBand.Endpoints.Response.RemoteHigherWindowTransfer
public import BlockBand.Endpoints.Poisson.SingleCollarAnalytic
public import BlockBand.Endpoints.Response.PathFractionalInverseMoment

/-!
# The energy parameters of the window transfer

* `rhwLamSq = β₀(e)/β₀(E)`, `rhwLam = √rhwLamSq > 0` (the Ginibre rescaling of the port bonds,
  matching the absorption of the leads);
* `rhwAlpha = λ²α₀(E) - α₀(e)` (the real part of the lead mismatch, carried by the end blocks);
* `rhwP = z(E)/(z(e)λ)` (the scalar between the two boundary-to-interior maps).
Then `α = λ²/z(E) - 1/z(e)` (`rhw_alpha_eq`) and the near clock at energy `e` is `|p|²` times the
near clock at `E` of the transformed sample (`rhw_nearClock_window`). Near `E` the parameters are
Lipschitz: `|λ² - 1|, |α| ≤ L|e - E|` (`rhw_params_lipschitz`), and `|p|² → 1`
(`rhw_tendsto_normSq_p`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Endpoints (nearClock)
open scoped ENNReal NNReal

/-- `λ² = β₀(e)/β₀(E)`, `1/z = α₀ - iβ₀`. -/
def rhwLamSq (b E e : ℝ) : ℝ := pfiBeta b e / pfiBeta b E

/-- `λ = √(β₀(e)/β₀(E))`. -/
def rhwLam (b E e : ℝ) : ℝ := Real.sqrt (rhwLamSq b E e)

/-- `α = λ²α₀(E) - α₀(e)`. -/
def rhwAlpha (b E e : ℝ) : ℝ := rhwLamSq b E e * pfiAlpha b E - pfiAlpha b e

/-- `p = z(E)/(z(e)λ)`. -/
def rhwP (b E e : ℝ) : ℂ := boundaryZ b E / (boundaryZ b e * rhwLam b E e)

variable {b E e : ℝ}

theorem rhw_lamSq_pos (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (he1 : -2 < e) (he2 : e < 2) :
    0 < rhwLamSq b E e :=
  div_pos (pfiBeta_pos hb he1 he2) (pfiBeta_pos hb hE1 hE2)

theorem rhw_lam_pos (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (he1 : -2 < e) (he2 : e < 2) :
    0 < rhwLam b E e :=
  Real.sqrt_pos.mpr (rhw_lamSq_pos hb hE1 hE2 he1 he2)

theorem rhw_lam_sq (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (he1 : -2 < e) (he2 : e < 2) :
    rhwLam b E e ^ 2 = rhwLamSq b E e :=
  Real.sq_sqrt (rhw_lamSq_pos hb hE1 hE2 he1 he2).le

theorem rhw_alpha_eq (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (he1 : -2 < e) (he2 : e < 2) :
    ((rhwAlpha b E e : ℝ) : ℂ) =
      (rhwLam b E e : ℂ) ^ 2 * (boundaryZ b E)⁻¹ - (boundaryZ b e)⁻¹ := by
  have hβ := (pfiBeta_pos hb hE1 hE2).ne'
  have hsq : (rhwLam b E e : ℂ) ^ 2 = ((rhwLamSq b E e : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, rhw_lam_sq hb hE1 hE2 he1 he2]
  rw [hsq, inv_boundaryZ_eq, inv_boundaryZ_eq]
  apply Complex.ext
  · simp [rhwAlpha]
  · simp only [rhwLamSq, Complex.ofReal_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    field_simp
    ring

/-- **The near clock at a moving energy** is `|p|²` times the near clock at `E` of the
transformed sample. -/
theorem rhw_nearClock_window (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (he1 : -2 < e)
    (he2 : e < 2) (W m : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    nearClock b e W m q ω = ((Complex.normSq (rhwP b E e) : ℝ) : ℂ) •
      rhwClock E (boundaryZ b E) W m q
        (rhwT (e - E) (rhwAlpha b E e) (rhwLam b E e) (pathAt W m ω)) := by
  rw [rhw_nearClock_eq]
  exact rhw_clock_transform (by ring) (rhw_lam_pos hb hE1 hE2 he1 he2).ne'
    (boundaryZ_ne_zero hb hE1 hE2) (boundaryZ_ne_zero hb he1 he2)
    (rhw_alpha_eq hb hE1 hE2 he1 he2) q _

/-- `1/z` is Lipschitz near a bulk energy. -/
theorem rhw_inv_boundaryZ_lipschitz (b : ℝ) (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ L η : ℝ, 0 ≤ L ∧ 0 < η ∧ ∀ e : ℝ, |e - E| < η →
      (-2 < e ∧ e < 2) ∧ ‖(boundaryZ b e)⁻¹ - (boundaryZ b E)⁻¹‖ ≤ L * |e - E| := by
  have hA := sca_analyticAt_boundaryZ b ⟨hE1, hE2⟩
  have hd := ((hA.inv (boundaryZ_ne_zero hb hE1 hE2)).differentiableAt).hasDerivAt
  obtain ⟨c, hc⟩ := hd.isBigO_sub.bound
  have hev := hc.and (isOpen_Ioo.mem_nhds ⟨hE1, hE2⟩)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨max c 0, η, le_max_right _ _, hη, fun e he => ?_⟩
  have h := hball (show dist e E < η by rwa [Real.dist_eq])
  refine ⟨h.2, ?_⟩
  refine h.1.trans ?_
  rw [Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)

/-- **The transform parameters are Lipschitz near `E`**: `|λ² - 1| ≤ L|e - E|`,
`|α| ≤ L|e - E|`. -/
theorem rhw_params_lipschitz (b : ℝ) (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ L η : ℝ, 0 ≤ L ∧ 0 < η ∧ ∀ e : ℝ, |e - E| < η →
      (-2 < e ∧ e < 2) ∧ |rhwLamSq b E e - 1| ≤ L * |e - E| ∧
        |rhwAlpha b E e| ≤ L * |e - E| := by
  obtain ⟨L, η, hL, hη, h⟩ := rhw_inv_boundaryZ_lipschitz b hb hE1 hE2
  have hβ := pfiBeta_pos hb hE1 hE2
  refine ⟨L / pfiBeta b E + (L / pfiBeta b E * |pfiAlpha b E| + L), η, by positivity, hη,
    fun e he => ?_⟩
  obtain ⟨he', hl⟩ := h e he
  have hdiff : (boundaryZ b e)⁻¹ - (boundaryZ b E)⁻¹ =
      (((pfiAlpha b e - pfiAlpha b E : ℝ)) : ℂ) - ((pfiBeta b e - pfiBeta b E : ℝ) : ℂ) *
        Complex.I := by
    rw [inv_boundaryZ_eq, inv_boundaryZ_eq]; push_cast; ring
  have hre : |pfiAlpha b e - pfiAlpha b E| ≤ L * |e - E| := by
    refine le_trans ?_ hl
    have := Complex.abs_re_le_norm ((boundaryZ b e)⁻¹ - (boundaryZ b E)⁻¹)
    rw [hdiff] at this ⊢
    simpa using this
  have him : |pfiBeta b e - pfiBeta b E| ≤ L * |e - E| := by
    refine le_trans ?_ hl
    have := Complex.abs_im_le_norm ((boundaryZ b e)⁻¹ - (boundaryZ b E)⁻¹)
    rw [hdiff] at this ⊢
    rw [abs_sub_comm]
    simpa using this
  have hlam : |rhwLamSq b E e - 1| ≤ L / pfiBeta b E * |e - E| := by
    have : rhwLamSq b E e - 1 = (pfiBeta b e - pfiBeta b E) / pfiBeta b E := by
      unfold rhwLamSq; field_simp
    rw [this, abs_div, abs_of_pos hβ, div_le_iff₀ hβ]
    calc _ ≤ L * |e - E| := him
      _ = _ := by field_simp
  have hab := abs_nonneg (e - E)
  refine ⟨he', hlam.trans (by nlinarith [mul_nonneg (div_nonneg hL hβ.le) (abs_nonneg
    (pfiAlpha b E))]), ?_⟩
  have halpha : rhwAlpha b E e = (rhwLamSq b E e - 1) * pfiAlpha b E +
      (pfiAlpha b E - pfiAlpha b e) := by unfold rhwAlpha; ring
  rw [halpha]
  calc |(rhwLamSq b E e - 1) * pfiAlpha b E + (pfiAlpha b E - pfiAlpha b e)|
      ≤ |rhwLamSq b E e - 1| * |pfiAlpha b E| + |pfiAlpha b e - pfiAlpha b E| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_sub_comm (pfiAlpha b E)]
    _ ≤ L / pfiBeta b E * |e - E| * |pfiAlpha b E| + L * |e - E| :=
        add_le_add (mul_le_mul_of_nonneg_right hlam (abs_nonneg _)) hre
    _ ≤ _ := by
        have : 0 ≤ L / pfiBeta b E * |e - E| := by positivity
        nlinarith [abs_nonneg (pfiAlpha b E)]

theorem rhw_continuousAt_p (b : ℝ) (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) :
    ContinuousAt (fun e => rhwP b E e) E := by
  have hz : ContinuousAt (fun e => boundaryZ b e) E :=
    (sca_analyticAt_boundaryZ b ⟨hE1, hE2⟩).continuousAt
  have hzi : ContinuousAt (fun e => (boundaryZ b e)⁻¹) E :=
    hz.inv₀ (boundaryZ_ne_zero hb hE1 hE2)
  have hβ : ContinuousAt (fun e => pfiBeta b e) E := by
    unfold pfiBeta
    exact (Complex.continuous_im.continuousAt.comp hzi).neg
  have hlam : ContinuousAt (fun e => rhwLam b E e) E := by
    unfold rhwLam rhwLamSq
    exact Real.continuous_sqrt.continuousAt.comp (hβ.div_const _)
  have hden : boundaryZ b E * (rhwLam b E E : ℂ) ≠ 0 := by
    refine mul_ne_zero (boundaryZ_ne_zero hb hE1 hE2) ?_
    exact_mod_cast (rhw_lam_pos hb hE1 hE2 hE1 hE2).ne'
  unfold rhwP
  exact continuousAt_const.div (hz.mul (Complex.continuous_ofReal.continuousAt.comp hlam)) hden

theorem rhw_p_self (b : ℝ) (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) : rhwP b E E = 1 := by
  have hβ := (pfiBeta_pos hb hE1 hE2).ne'
  unfold rhwP rhwLam rhwLamSq
  rw [div_self hβ, Real.sqrt_one, Complex.ofReal_one, mul_one,
    div_self (boundaryZ_ne_zero hb hE1 hE2)]

/-- `|p(e_W)|² → 1` along energies `e_W → E`. -/
theorem rhw_tendsto_normSq_p (b : ℝ) (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 E)) :
    Tendsto (fun W => Complex.normSq (rhwP b E (e W))) atTop (𝓝 1) := by
  have h := ((Complex.continuous_normSq.continuousAt).comp (rhw_continuousAt_p b hb hE1 hE2)).tendsto.comp he
  have h1 : (Complex.normSq ∘ fun e => rhwP b E e) E = 1 := by
    simp only [Function.comp, rhw_p_self b hb hE1 hE2, Complex.normSq_one]
  rw [h1] at h
  exact h

end BlockBand.Endpoints
