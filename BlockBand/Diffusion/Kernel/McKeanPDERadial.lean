module

public import BlockBand.Diffusion.Kernel.McKeanPDEPoint
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The radial heat equation for McKean's kernel

Lebesgue measure on `(0, ∞)` in the variable `v`. For `T > 0` and `c > 1` (where the clamp
`max c 1` of `mkHypKernel` is inactive near `c`) put `w = c + v²` and
`F_j(T, c) = ∫_0^∞ G^{(j)}_T(c + v²) dv` (`mkF0`, `mkF1`, `mkF2`, `mkFT` for `G`, `∂_w G`,
`∂_w² G`, `∂_T G`; closed forms in `McKeanPDEPoint`). Then `mkHypKernel T c = A_T F₀(T, c)`
with `A_T = mkA T`, and:
* `mk_hasDerivAt_hypKernel`: `∂_c K_T(c) = mkK1 T c = A_T F₁(T, c)`;
* `mk_hasDerivAt_k1`: `∂_c (mkK1 T) c = mkK2 T c = A_T F₂(T, c)`;
* `mk_hasDerivAt_hypKernel_T` (**radial heat equation**):
  `∂_T K_T(c) = (c² - 1) mkK2 T c + 2 c mkK1 T c`, i.e. `∂_T K = (c²-1) ∂_c² K + 2c ∂_c K`
  (`mk_hypKernel_radial_pde`, stated with `deriv`).

The proof is a descent from `H³`: the pointwise `H³` equation `mk_gT_eq`, and the exact
identity `(c² - 1) F₂ + 2c F₁ = ∫ [(w² - 1) G'' + 3 w G'](c + v²) dv + (3/4) F₀`
(`mk_fT_eq`), obtained from the antiderivative
`Φ(v) = (v/2)(2c + v²) G'(c + v²) + (3/4) v G(c + v²)` (`Φ(0) = 0`, `Φ(∞) = 0`).
Differentiation under the integral uses the uniform majorant `mkBd · (1 + v²)⁻¹` from
`mk_gw_le`, valid for `c ≥ c₀ > 1` and `T` in compact subsets of `(0, ∞)`.
We also record the explicit bounds `|F_j(T, c)| ≤ mkBd T₁ T₂ c₀ · π/2`
(`mk_abs_f_le`) and joint continuity of `F₁, F₂` on `(0,∞) × (1,∞)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real

/-!
### The `v`-integrals
-/

/-- `F₀(T, c) = ∫_0^∞ G_T(c + v²) dv` (no clamp). -/
def mkF0 (T c : ℝ) : ℝ := ∫ v in Ioi (0 : ℝ), mkMcKeanG T (c + v ^ 2)

/-- `F₁(T, c) = ∫_0^∞ ∂_w G_T(c + v²) dv`. -/
def mkF1 (T c : ℝ) : ℝ := ∫ v in Ioi (0 : ℝ), mkGw1 T (c + v ^ 2)

/-- `F₂(T, c) = ∫_0^∞ ∂_w² G_T(c + v²) dv`. -/
def mkF2 (T c : ℝ) : ℝ := ∫ v in Ioi (0 : ℝ), mkGw2 T (c + v ^ 2)

/-- `F_T(T, c) = ∫_0^∞ ∂_T G_T(c + v²) dv`. -/
def mkFT (T c : ℝ) : ℝ := ∫ v in Ioi (0 : ℝ), mkGT T (c + v ^ 2)

/-- `∂_c K_T(c)` for `c > 1`. -/
def mkK1 (T c : ℝ) : ℝ := mkA T * mkF1 T c

/-- `∂_c² K_T(c)` for `c > 1`. -/
def mkK2 (T c : ℝ) : ℝ := mkA T * mkF2 T c

theorem mk_gw1_measurable (T : ℝ) : Measurable (mkGw1 T) := by
  have := mk_arcosh_measurable
  unfold mkGw1 mkN1
  fun_prop

theorem mk_gw2_measurable (T : ℝ) : Measurable (mkGw2 T) := by
  have := mk_arcosh_measurable
  unfold mkGw2 mkN2 mkN1 mkN1d
  fun_prop

theorem mk_gT_measurable (T : ℝ) : Measurable (mkGT T) := by
  have := mk_arcosh_measurable
  have := mk_mcKeanG_measurable T
  unfold mkGT
  fun_prop

theorem mk_inv_pow_six_le {c₀ c v : ℝ} (hc₀ : 1 < c₀) (hc : c₀ ≤ c) :
    ((c + v ^ 2) ^ 6)⁻¹ ≤ (1 + v ^ 2)⁻¹ := by
  apply inv_anti₀ (by positivity)
  have h1 : 1 + v ^ 2 ≤ c + v ^ 2 := by linarith
  have h2 : 1 ≤ c + v ^ 2 := by nlinarith [sq_nonneg v]
  calc 1 + v ^ 2 ≤ c + v ^ 2 := h1
    _ = (c + v ^ 2) ^ 1 := (pow_one _).symm
    _ ≤ (c + v ^ 2) ^ 6 := pow_le_pow_right₀ h2 (by norm_num)

/-- The six integrands are dominated by `mkBd T₁ T₂ c₀ · (1 + v²)⁻¹`. -/
theorem mk_gw_le_inv {T₁ T₂ T c₀ c : ℝ} (hT₁ : 0 < T₁) (h₁ : T₁ ≤ T) (h₂ : T ≤ T₂)
    (hc₀ : 1 < c₀) (hc : c₀ ≤ c) (v : ℝ) :
    |mkMcKeanG T (c + v ^ 2)| ≤ mkBd T₁ T₂ c₀ * (1 + v ^ 2)⁻¹ ∧
      |mkGw1 T (c + v ^ 2)| ≤ mkBd T₁ T₂ c₀ * (1 + v ^ 2)⁻¹ ∧
      |mkGw2 T (c + v ^ 2)| ≤ mkBd T₁ T₂ c₀ * (1 + v ^ 2)⁻¹ ∧
      |mkGT T (c + v ^ 2)| ≤ mkBd T₁ T₂ c₀ * (1 + v ^ 2)⁻¹ ∧
      |mkGTT T (c + v ^ 2)| ≤ mkBd T₁ T₂ c₀ * (1 + v ^ 2)⁻¹ ∧
      |mkGTw T (c + v ^ 2)| ≤ mkBd T₁ T₂ c₀ * (1 + v ^ 2)⁻¹ := by
  have hw : c₀ ≤ c + v ^ 2 := by nlinarith [sq_nonneg v]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := mk_gw_le hT₁ h₁ h₂ hc₀ hw
  have hi := mk_inv_pow_six_le (v := v) hc₀ hc
  have hB := mk_bd_nonneg (T₂ := T₂) hT₁ hc₀
  exact ⟨h0.trans (by gcongr), h1.trans (by gcongr), h2.trans (by gcongr),
    h3.trans (by gcongr), h4.trans (by gcongr), h5.trans (by gcongr)⟩

theorem mk_integrableOn_of_le {h : ℝ → ℝ} (hm : Measurable h) {B : ℝ}
    (hb : ∀ v, |h v| ≤ B * (1 + v ^ 2)⁻¹) : IntegrableOn h (Ioi 0) :=
  Integrable.mono' (integrable_inv_one_add_sq.const_mul B).integrableOn
    hm.aestronglyMeasurable (ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact hb v)

theorem mk_measurable_shift {f : ℝ → ℝ} (hf : Measurable f) (c : ℝ) :
    Measurable fun v : ℝ => f (c + v ^ 2) :=
  hf.comp (by fun_prop)

/-- Integrability of the four integrands for `T > 0`, `c > 1`. -/
theorem mk_integrableOn_gw {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    IntegrableOn (fun v => mkMcKeanG T (c + v ^ 2)) (Ioi 0) ∧
      IntegrableOn (fun v => mkGw1 T (c + v ^ 2)) (Ioi 0) ∧
      IntegrableOn (fun v => mkGw2 T (c + v ^ 2)) (Ioi 0) ∧
      IntegrableOn (fun v => mkGT T (c + v ^ 2)) (Ioi 0) := by
  have hb := fun v => mk_gw_le_inv hT le_rfl le_rfl hc le_rfl (c := c) v
  exact ⟨mk_integrableOn_of_le (mk_measurable_shift (mk_mcKeanG_measurable T) c)
      fun v => (hb v).1,
    mk_integrableOn_of_le (mk_measurable_shift (mk_gw1_measurable T) c) fun v => (hb v).2.1,
    mk_integrableOn_of_le (mk_measurable_shift (mk_gw2_measurable T) c) fun v => (hb v).2.2.1,
    mk_integrableOn_of_le (mk_measurable_shift (mk_gT_measurable T) c) fun v => (hb v).2.2.2.1⟩

theorem mk_integral_inv_one_add_sq_Ioi : ∫ v in Ioi (0 : ℝ), (1 + v ^ 2)⁻¹ = π / 2 := by
  rw [integral_Ioi_inv_one_add_sq, Real.arctan_zero]; ring

/-- Explicit bounds: `|F_j(T, c)| ≤ mkBd T₁ T₂ c₀ · π/2` for `T ∈ [T₁, T₂]`, `c ≥ c₀ > 1`. -/
theorem mk_abs_f_le {T₁ T₂ T c₀ c : ℝ} (hT₁ : 0 < T₁) (h₁ : T₁ ≤ T) (h₂ : T ≤ T₂)
    (hc₀ : 1 < c₀) (hc : c₀ ≤ c) :
    |mkF0 T c| ≤ mkBd T₁ T₂ c₀ * (π / 2) ∧ |mkF1 T c| ≤ mkBd T₁ T₂ c₀ * (π / 2) ∧
      |mkF2 T c| ≤ mkBd T₁ T₂ c₀ * (π / 2) ∧ |mkFT T c| ≤ mkBd T₁ T₂ c₀ * (π / 2) := by
  have hb := fun v => mk_gw_le_inv hT₁ h₁ h₂ hc₀ hc v
  have hI : ∫ v in Ioi (0 : ℝ), mkBd T₁ T₂ c₀ * (1 + v ^ 2)⁻¹ = mkBd T₁ T₂ c₀ * (π / 2) := by
    rw [integral_const_mul, mk_integral_inv_one_add_sq_Ioi]
  have key : ∀ f : ℝ → ℝ, (∀ v, |f v| ≤ mkBd T₁ T₂ c₀ * (1 + v ^ 2)⁻¹) →
      |∫ v in Ioi (0 : ℝ), f v| ≤ mkBd T₁ T₂ c₀ * (π / 2) := fun f hf => by
    rw [← hI]
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (ae_of_all _ fun v => abs_nonneg _)
      (integrable_inv_one_add_sq.const_mul _).integrableOn (ae_of_all _ fun v => hf v)
  exact ⟨key _ fun v => (hb v).1, key _ fun v => (hb v).2.1, key _ fun v => (hb v).2.2.1,
    key _ fun v => (hb v).2.2.2.1⟩

/-!
### Differentiation under the integral
-/

theorem mk_ioo_mem_nhds {c : ℝ} (hc : 1 < c) : Ioo ((1 + c) / 2) (c + 1) ∈ 𝓝 c :=
  Ioo_mem_nhds (by linarith) (by linarith)

theorem mk_hasDerivAt_f0 {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (mkF0 T) (mkF1 T c) c := by
  have hc₀ : 1 < (1 + c) / 2 := by linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (mk_ioo_mem_nhds hc)
    (Eventually.of_forall fun c' =>
      (mk_measurable_shift (mk_mcKeanG_measurable T) c').aestronglyMeasurable)
    (mk_integrableOn_gw hT hc).1
    (mk_measurable_shift (mk_gw1_measurable T) c).aestronglyMeasurable
    (bound := fun v => mkBd T T ((1 + c) / 2) * (1 + v ^ 2)⁻¹)
    (ae_of_all _ fun v c' hc' => by
      rw [Real.norm_eq_abs]; exact (mk_gw_le_inv hT le_rfl le_rfl hc₀ hc'.1.le v).2.1)
    (integrable_inv_one_add_sq.const_mul _).integrableOn
    (ae_of_all _ fun v c' hc' => ?_)).2
  have hw : 1 < c' + v ^ 2 := by nlinarith [hc'.1, sq_nonneg v]
  exact HasDerivAt.comp_add_const c' (v ^ 2) (mk_hasDerivAt_mcKeanG hT.ne' hw)

theorem mk_hasDerivAt_f1 {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (mkF1 T) (mkF2 T c) c := by
  have hc₀ : 1 < (1 + c) / 2 := by linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (mk_ioo_mem_nhds hc)
    (Eventually.of_forall fun c' =>
      (mk_measurable_shift (mk_gw1_measurable T) c').aestronglyMeasurable)
    (mk_integrableOn_gw hT hc).2.1
    (mk_measurable_shift (mk_gw2_measurable T) c).aestronglyMeasurable
    (bound := fun v => mkBd T T ((1 + c) / 2) * (1 + v ^ 2)⁻¹)
    (ae_of_all _ fun v c' hc' => by
      rw [Real.norm_eq_abs]; exact (mk_gw_le_inv hT le_rfl le_rfl hc₀ hc'.1.le v).2.2.1)
    (integrable_inv_one_add_sq.const_mul _).integrableOn
    (ae_of_all _ fun v c' hc' => ?_)).2
  have hw : 1 < c' + v ^ 2 := by nlinarith [hc'.1, sq_nonneg v]
  exact HasDerivAt.comp_add_const c' (v ^ 2) (mk_hasDerivAt_gw1 hT.ne' hw)

theorem mk_hasDerivAt_f0_T {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (fun T' => mkF0 T' c) (mkFT T c) T := by
  have hs : Ioo (T / 2) (2 * T) ∈ 𝓝 T := Ioo_mem_nhds (by linarith) (by linarith)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall fun T' =>
      (mk_measurable_shift (mk_mcKeanG_measurable T') c).aestronglyMeasurable)
    (mk_integrableOn_gw hT hc).1
    (mk_measurable_shift (mk_gT_measurable T) c).aestronglyMeasurable
    (bound := fun v => mkBd (T / 2) (2 * T) c * (1 + v ^ 2)⁻¹)
    (ae_of_all _ fun v T' hT' => by
      rw [Real.norm_eq_abs]
      exact (mk_gw_le_inv (by linarith) hT'.1.le hT'.2.le hc le_rfl v).2.2.2.1)
    (integrable_inv_one_add_sq.const_mul _).integrableOn
    (ae_of_all _ fun v T' hT' => ?_)).2
  exact mk_hasDerivAt_mcKeanG_T (by linarith [hT'.1] : T' ≠ 0).symm.symm

/-!
### The `H³` descent identity
-/

/-- The antiderivative `Φ(v) = (v/2)(2c + v²) G'(c + v²) + (3/4) v G(c + v²)`. -/
def mkPhi (T c v : ℝ) : ℝ :=
  v / 2 * (2 * c + v ^ 2) * mkGw1 T (c + v ^ 2) + 3 / 4 * v * mkMcKeanG T (c + v ^ 2)

theorem mk_hasDerivAt_phi {T c : ℝ} (hT : T ≠ 0) (hc : 1 < c) (v : ℝ) :
    HasDerivAt (mkPhi T c)
      (v ^ 2 * (2 * c + v ^ 2) * mkGw2 T (c + v ^ 2) + (c + 3 * v ^ 2) * mkGw1 T (c + v ^ 2) +
        3 / 4 * mkMcKeanG T (c + v ^ 2)) v := by
  have hw : 1 < c + v ^ 2 := by nlinarith [sq_nonneg v]
  have hq : HasDerivAt (fun u : ℝ => c + u ^ 2) (2 * v) v := by
    simpa using (hasDerivAt_pow 2 v).const_add c
  have h1 := (mk_hasDerivAt_gw1 hT hw).comp v hq
  have h0 := (mk_hasDerivAt_mcKeanG hT hw).comp v hq
  have hp : HasDerivAt (fun u : ℝ => u / 2 * (2 * c + u ^ 2)) (1 / 2 * (2 * c + v ^ 2) +
      v / 2 * (2 * v)) v := by
    have := ((hasDerivAt_id v).div_const 2).mul ((hasDerivAt_pow 2 v).const_add (2 * c))
    convert this using 1
    · funext u; simp only [Pi.mul_apply, id_eq]
    · simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  have h := (hp.mul h1).add (((hasDerivAt_id v).const_mul (3 / 4)).mul h0)
  convert h using 1
  · funext u; simp only [mkPhi, Pi.mul_apply, Pi.add_apply, Function.comp_apply, id_eq]
  · simp only [id_eq, Function.comp_apply]
    ring

theorem mk_phi_tendsto {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    Tendsto (mkPhi T c) atTop (𝓝 0) := by
  set B := mkBd T T c
  have hB : 0 ≤ B := mk_bd_nonneg hT hc
  have hlim : Tendsto (fun v : ℝ => 2 * B / v) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
  have hv0 : 0 < v := by linarith
  set w := c + v ^ 2 with hwdef
  have hw : c ≤ w := by nlinarith [sq_nonneg v]
  obtain ⟨h0, h1, -⟩ := mk_gw_le hT le_rfl le_rfl hc hw
  have hw1 : 1 ≤ w := by linarith
  have hw4 : 0 < w ^ 4 := by positivity
  have h64 : B * (w ^ 6)⁻¹ ≤ B * (w ^ 4)⁻¹ :=
    mul_le_mul_of_nonneg_left (inv_anti₀ hw4 (pow_le_pow_right₀ hw1 (by norm_num))) hB
  replace h0 := h0.trans h64
  replace h1 := h1.trans h64
  have hA : v / 2 * (2 * c + v ^ 2) * (w ^ 4)⁻¹ ≤ 1 / v := by
    have hw2 : w ^ 2 ≤ w ^ 4 := pow_le_pow_right₀ hw1 (by norm_num)
    have h2 : v * (2 * c + v ^ 2) * v ≤ 2 * w ^ 2 := by nlinarith
    have key : v * (2 * c + v ^ 2) * v ≤ 2 * w ^ 4 := by linarith
    calc v / 2 * (2 * c + v ^ 2) * (w ^ 4)⁻¹ = (v * (2 * c + v ^ 2) * v) / (2 * w ^ 4 * v) := by
          field_simp
      _ ≤ (2 * w ^ 4) / (2 * w ^ 4 * v) := by gcongr
      _ = 1 / v := by field_simp
  have hB' : 3 / 4 * v * (w ^ 4)⁻¹ ≤ 1 / v := by
    have hw2 : v ^ 2 ≤ w := by linarith
    have hw2' : w ≤ w ^ 4 := by
      calc w = w ^ 1 := (pow_one w).symm
        _ ≤ w ^ 4 := pow_le_pow_right₀ hw1 (by norm_num)
    have key : 3 / 4 * v * v ≤ w ^ 4 := by nlinarith
    calc 3 / 4 * v * (w ^ 4)⁻¹ = (3 / 4 * v * v) / (w ^ 4 * v) := by field_simp
      _ ≤ w ^ 4 / (w ^ 4 * v) := by gcongr
      _ = 1 / v := by field_simp
  rw [Real.norm_eq_abs]
  unfold mkPhi
  rw [← hwdef]
  calc |v / 2 * (2 * c + v ^ 2) * mkGw1 T w + 3 / 4 * v * mkMcKeanG T w|
      ≤ |v / 2 * (2 * c + v ^ 2) * mkGw1 T w| + |3 / 4 * v * mkMcKeanG T w| := abs_add_le _ _
    _ = v / 2 * (2 * c + v ^ 2) * |mkGw1 T w| + 3 / 4 * v * |mkMcKeanG T w| := by
        rw [abs_mul, abs_mul (3 / 4 * v),
          abs_of_nonneg (by positivity : 0 ≤ v / 2 * (2 * c + v ^ 2)),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / 4 * v)]
    _ ≤ v / 2 * (2 * c + v ^ 2) * (B * (w ^ 4)⁻¹) + 3 / 4 * v * (B * (w ^ 4)⁻¹) := by
        gcongr
    _ = B * (v / 2 * (2 * c + v ^ 2) * (w ^ 4)⁻¹) + B * (3 / 4 * v * (w ^ 4)⁻¹) := by ring
    _ ≤ B * (1 / v) + B * (1 / v) := by gcongr
    _ = 2 * B / v := by ring

/-- **The descent identity.** For `T > 0`, `c > 1`:
`F_T = (c² - 1) F₂ + 2 c F₁ + (3/(2T) + 1/4) F₀`. -/
theorem mk_fT_eq {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    mkFT T c = (c ^ 2 - 1) * mkF2 T c + 2 * c * mkF1 T c + (3 / (2 * T) + 1 / 4) * mkF0 T c := by
  obtain ⟨i0, i1, i2, iT⟩ := mk_integrableOn_gw hT hc
  set D : ℝ → ℝ := fun v => v ^ 2 * (2 * c + v ^ 2) * mkGw2 T (c + v ^ 2) +
    (c + 3 * v ^ 2) * mkGw1 T (c + v ^ 2) + 3 / 4 * mkMcKeanG T (c + v ^ 2) with hD
  have hDeq : ∀ v, D v = mkGT T (c + v ^ 2) - (c ^ 2 - 1) * mkGw2 T (c + v ^ 2) -
      2 * c * mkGw1 T (c + v ^ 2) - (3 / (2 * T) + 1 / 4) * mkMcKeanG T (c + v ^ 2) := by
    intro v
    have hw : 1 < c + v ^ 2 := by nlinarith [sq_nonneg v]
    rw [mk_gT_eq hT.ne' hw, hD]
    ring
  have hDint : IntegrableOn D (Ioi 0) := by
    have : D = fun v => mkGT T (c + v ^ 2) - (c ^ 2 - 1) * mkGw2 T (c + v ^ 2) -
        2 * c * mkGw1 T (c + v ^ 2) - (3 / (2 * T) + 1 / 4) * mkMcKeanG T (c + v ^ 2) :=
      funext hDeq
    rw [this]
    exact ((iT.sub (i2.const_mul _)).sub (i1.const_mul _)).sub (i0.const_mul _)
  have hFTC : ∫ v in Ioi (0 : ℝ), D v = 0 - mkPhi T c 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun v _ => mk_hasDerivAt_phi hT.ne' hc v) hDint
      (mk_phi_tendsto hT hc)
  have hphi0 : mkPhi T c 0 = 0 := by simp [mkPhi]
  rw [hphi0, sub_zero] at hFTC
  have hsplit : ∫ v in Ioi (0 : ℝ), D v = mkFT T c - (c ^ 2 - 1) * mkF2 T c -
      2 * c * mkF1 T c - (3 / (2 * T) + 1 / 4) * mkF0 T c := by
    rw [integral_congr_ae (ae_of_all _ hDeq), integral_sub, integral_sub, integral_sub,
      integral_const_mul, integral_const_mul, integral_const_mul]
    · rfl
    · exact iT
    · exact i2.const_mul _
    · exact iT.sub (i2.const_mul _)
    · exact i1.const_mul _
    · exact (iT.sub (i2.const_mul _)).sub (i1.const_mul _)
    · exact i0.const_mul _
  linarith

/-!
### The kernel
-/

theorem mk_hypKernel_eq_f0 {T c : ℝ} (hc : 1 ≤ c) : mkHypKernel T c = mkA T * mkF0 T c := by
  rw [mk_hypKernel_eq_mkA, max_eq_left hc]; rfl

theorem mk_hasDerivAt_mkA {T : ℝ} (hT : 0 < T) :
    HasDerivAt mkA (mkA T * (-1 / 4 - 3 / (2 * T))) T := by
  have hb : 0 < 4 * π * T := by positivity
  have hr : HasDerivAt (fun T' : ℝ => (4 * π * T') ^ (3 / 2 : ℝ))
      (4 * π * (3 / 2 : ℝ) * (4 * π * T) ^ ((3 / 2 : ℝ) - 1)) T := by
    have := ((hasDerivAt_id T).const_mul (4 * π)).rpow_const (p := (3 / 2 : ℝ))
      (Or.inl (by simpa using hb.ne'))
    simpa using this
  have he : HasDerivAt (fun T' : ℝ => Real.exp (-T' / 4)) (Real.exp (-T / 4) * (-1 / 4)) T := by
    have := ((hasDerivAt_id T).neg.div_const 4).exp
    simpa [neg_div] using this
  have hrp : 0 < (4 * π * T) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hb _
  have h := (he.const_mul (Real.sqrt 2)).div hr hrp.ne'
  unfold mkA
  convert h using 1
  rw [Real.rpow_sub_one hb.ne']
  field_simp

/-- `∂_c K_T(c) = mkK1 T c` for `T > 0`, `c > 1`. -/
theorem mk_hasDerivAt_hypKernel {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (mkHypKernel T) (mkK1 T c) c := by
  have heq : mkHypKernel T =ᶠ[𝓝 c] fun c' => mkA T * mkF0 T c' := by
    filter_upwards [lt_mem_nhds hc] with c' hc'
    exact mk_hypKernel_eq_f0 hc'.le
  exact ((mk_hasDerivAt_f0 hT hc).const_mul (mkA T)).congr_of_eventuallyEq heq

/-- `∂_c mkK1 T c = mkK2 T c` for `T > 0`, `c > 1`. -/
theorem mk_hasDerivAt_k1 {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (mkK1 T) (mkK2 T c) c :=
  (mk_hasDerivAt_f1 hT hc).const_mul (mkA T)

/-- **Radial heat equation.** For `T > 0`, `c > 1`:
`∂_T K_T(c) = (c² - 1) ∂_c² K_T(c) + 2 c ∂_c K_T(c)`, with `∂_c K = mkK1`, `∂_c² K = mkK2`. -/
theorem mk_hasDerivAt_hypKernel_T {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    HasDerivAt (fun T' => mkHypKernel T' c) ((c ^ 2 - 1) * mkK2 T c + 2 * c * mkK1 T c) T := by
  have heq : (fun T' => mkHypKernel T' c) = fun T' => mkA T' * mkF0 T' c :=
    funext fun T' => mk_hypKernel_eq_f0 hc.le
  rw [heq]
  convert (mk_hasDerivAt_mkA hT).mul (mk_hasDerivAt_f0_T hT hc) using 1
  rw [mk_fT_eq hT hc]
  unfold mkK1 mkK2
  ring

theorem mk_deriv_hypKernel {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    deriv (mkHypKernel T) c = mkK1 T c :=
  (mk_hasDerivAt_hypKernel hT hc).deriv

theorem mk_deriv_deriv_hypKernel {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    deriv (deriv (mkHypKernel T)) c = mkK2 T c := by
  have heq : deriv (mkHypKernel T) =ᶠ[𝓝 c] mkK1 T := by
    filter_upwards [lt_mem_nhds hc] with c' hc'
    exact mk_deriv_hypKernel hT hc'
  rw [heq.deriv_eq]
  exact (mk_hasDerivAt_k1 hT hc).deriv

/-- **Radial heat equation in `deriv` form.** For `T > 0` and `c > 1`:
`∂_T K_T(c) = (c² - 1) ∂_c² K_T(c) + 2 c ∂_c K_T(c)`. -/
theorem mk_hypKernel_radial_pde {T c : ℝ} (hT : 0 < T) (hc : 1 < c) :
    deriv (fun T' => mkHypKernel T' c) T =
      (c ^ 2 - 1) * deriv (deriv (mkHypKernel T)) c + 2 * c * deriv (mkHypKernel T) c := by
  rw [(mk_hasDerivAt_hypKernel_T hT hc).deriv, mk_deriv_deriv_hypKernel hT hc,
    mk_deriv_hypKernel hT hc]

end BlockBand.Diffusion
