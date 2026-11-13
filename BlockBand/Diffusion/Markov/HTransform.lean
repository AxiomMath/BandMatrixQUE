module

public import BlockBand.Diffusion.Markov.Semigroup

/-!
# Killing by an excessive function: the Doob `h`-transform of a transition density

For transition densities `p` relative to `μ` and `h : E → ℝ≥0∞`, the **`h`-transformed (killed)
density** is `hTransform p h t a b = p_t(a, b) h(b) / h(a)`. The function `h` is **excessive on
`S`** (`IsExcessiveOn μ S p h`) if `P_t h(a) = ∫⁻ p_t(a, b) h(b) dμ(b) ≤ h(a)` for `t > 0`,
`a ∈ S`; harmonic if equality holds. The **killed finite-dimensional density** (the law of
`(Z_{t₁}, …, Z_{t_k})` on `{t_k < ζ}` for the `h`-transform from `z`) is
`doobFddDensity p h z ts zs = Πp(ts)(zs) · h(z_k)/h(z)`; this is the shape of
`LbkDoobKilledLaw` (`lbkFddProd ⋯ · (x + y) H(z_k)`, with `H(z) = (x + y)⁻¹`).

**Proved here** (`h` measurable, `0 < h < ∞` μ-a.e.; no positivity of `h` off a μ-null set
is needed, and none at all at the start except where stated):
* `lintegral_hTransform`: the mass `P^h_t 1(a) = P_t h(a) / h(a)`;
* `hTransform_isSubMarkovOn`: excessive `h` gives a sub-Markov density, `P^h_t 1 ≤ 1`;
  `hTransform_isMarkovOn`: harmonic `h` (finite, nonzero on `S`) gives a Markov density;
* `hTransform_isCKDensity`: Chapman–Kolmogorov for `p^h` on the same state space;
* `fddDensity_hTransform`: the telescoping `Πp^h = Πp · h(z_k)/h(z)` (pointwise when the
  `h(zᵢ)` and `h(z)` are in `(0, ∞)`), `ae_fddDensity_hTransform` (μ^k-a.e.),
  `fddMeasure_hTransform`: the finite-dimensional law of the `h`-transform is
  `μ^k.withDensity (doobFddDensity p h z ts)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E]

/-- **The `h`-transformed transition density** `p_t(a, b) h(b) / h(a)`. -/
def hTransform (p : ℝ → E → E → ℝ≥0∞) (h : E → ℝ≥0∞) : ℝ → E → E → ℝ≥0∞ :=
  fun t a b => p t a b * h b / h a

/-- `h` is excessive on `S`: `P_t h ≤ h` on `S` for `t > 0`. -/
def IsExcessiveOn (μ : Measure E) (S : Set E) (p : ℝ → E → E → ℝ≥0∞) (h : E → ℝ≥0∞) : Prop :=
  ∀ t, 0 < t → ∀ a ∈ S, ∫⁻ b, p t a b * h b ∂μ ≤ h a

/-- `h` is harmonic on `S`: `P_t h = h` on `S` for `t > 0`. -/
def IsHarmonicOn (μ : Measure E) (S : Set E) (p : ℝ → E → E → ℝ≥0∞) (h : E → ℝ≥0∞) : Prop :=
  ∀ t, 0 < t → ∀ a ∈ S, ∫⁻ b, p t a b * h b ∂μ = h a

/-- **The killed finite-dimensional density** of the `h`-transform from `z`:
`Πp(ts)(zs) · h(z_k) / h(z)`. -/
def doobFddDensity (p : ℝ → E → E → ℝ≥0∞) (h : E → ℝ≥0∞) (z : E) {k : ℕ} (ts : Fin k → ℝ)
    (zs : Fin k → E) : ℝ≥0∞ :=
  fddDensity p z ts zs * (h (lastPoint z zs) / h z)

theorem IsHarmonicOn.isExcessiveOn {μ : Measure E} {S : Set E} {p : ℝ → E → E → ℝ≥0∞}
    {h : E → ℝ≥0∞} (hh : IsHarmonicOn μ S p h) : IsExcessiveOn μ S p h :=
  fun t ht a ha => (hh t ht a ha).le

section Transform

variable {μ : Measure E} {S : Set E} {p : ℝ → E → E → ℝ≥0∞} {h : E → ℝ≥0∞}

theorem measurable_hTransform (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2)
    (hh : Measurable h) (t : ℝ) : Measurable fun q : E × E => hTransform p h t q.1 q.2 :=
  ((hp t).mul (hh.comp measurable_snd)).div (hh.comp measurable_fst)

/-- **The mass of the `h`-transform**: `∫⁻ p^h_t(a, ·) dμ = P_t h(a) / h(a)`. -/
theorem lintegral_hTransform (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2)
    (hh : Measurable h) (t : ℝ) (a : E) :
    ∫⁻ b, hTransform p h t a b ∂μ = (∫⁻ b, p t a b * h b ∂μ) / h a := by
  simp only [hTransform, div_eq_mul_inv]
  exact lintegral_mul_const _ (((hp t).comp (measurable_const.prodMk measurable_id)).mul hh)

/-- **Excessive functions give sub-Markov `h`-transforms**: `P^h_t 1 = P_t h / h ≤ 1`. -/
theorem hTransform_isSubMarkovOn (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2)
    (hh : Measurable h) (hex : IsExcessiveOn μ S p h) : IsSubMarkovOn μ S (hTransform p h) := by
  intro t ht a ha
  rw [lintegral_hTransform hp hh]
  exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hex t ht a ha)

/-- **Harmonic functions give Markov `h`-transforms** (where `0 < h < ∞`). -/
theorem hTransform_isMarkovOn (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2)
    (hh : Measurable h) (hhar : IsHarmonicOn μ S p h) (hS : ∀ a ∈ S, h a ≠ 0 ∧ h a ≠ ⊤) :
    IsMarkovOn μ S (hTransform p h) := by
  intro t ht a ha
  rw [lintegral_hTransform hp hh, hhar t ht a ha]
  exact ENNReal.div_self (hS a ha).1 (hS a ha).2

/-- **Chapman–Kolmogorov for the `h`-transform** (on the same state space), when `h` is
measurable and `0 < h < ∞` μ-a.e. -/
theorem hTransform_isCKDensity (hp : IsCKDensity μ S p) (hh : Measurable h)
    (hpos : ∀ᵐ y ∂μ, h y ≠ 0 ∧ h y ≠ ⊤) : IsCKDensity μ S (hTransform p h) where
  meas := measurable_hTransform hp.meas hh
  stays := by
    intro t ht a ha
    filter_upwards [hp.stays t ht a ha] with y hy hne
    refine hy fun h0 => hne ?_
    simp [hTransform, h0]
  ck := by
    intro s t hs ht a ha b
    have hint : ∀ᵐ y ∂μ, hTransform p h s a y * hTransform p h t y b =
        (p s a y * p t y b) * (h b * (h a)⁻¹) := by
      filter_upwards [hpos] with y hy
      have hc : h y * (h y)⁻¹ = 1 := ENNReal.mul_inv_cancel hy.1 hy.2
      simp only [hTransform, div_eq_mul_inv]
      calc p s a y * h y * (h a)⁻¹ * (p t y b * h b * (h y)⁻¹)
          = (p s a y * p t y b) * (h b * (h a)⁻¹) * (h y * (h y)⁻¹) := by ring
        _ = _ := by rw [hc, mul_one]
    rw [lintegral_congr_ae hint, lintegral_mul_const (f := fun y => p s a y * p t y b) _
      (((hp.meas s).comp
      (measurable_const.prodMk measurable_id)).mul ((hp.meas t).comp
      (measurable_id.prodMk measurable_const))), hp.ck s t hs ht a ha b]
    simp only [hTransform, div_eq_mul_inv]
    ring

end Transform

/-!
### The telescoping of the finite-dimensional densities
-/

section Telescope

variable {p : ℝ → E → E → ℝ≥0∞} {h : E → ℝ≥0∞}

omit [MeasurableSpace E] in
/-- **The telescoping** `Π p^h(ts)(zs) = Π p(ts)(zs) · h(z_k) / h(z)` when `h(z)` and all
`h(zᵢ)` are in `(0, ∞)`. -/
theorem fddDensity_hTransform :
    ∀ {k : ℕ} {z : E}, h z ≠ 0 → h z ≠ ⊤ → ∀ (ts : Fin k → ℝ) (zs : Fin k → E),
      (∀ i, h (zs i) ≠ 0 ∧ h (zs i) ≠ ⊤) →
        fddDensity (hTransform p h) z ts zs = doobFddDensity p h z ts zs := by
  intro k
  induction k with
  | zero =>
    intro z h0 htop ts zs _
    rw [doobFddDensity, fddDensity_zero, fddDensity_zero, lastPoint_zero,
      ENNReal.div_self h0 htop, mul_one]
  | succ m ih =>
    intro z h0 htop ts zs hzs
    rw [fddDensity_succ, ih (hzs 0).1 (hzs 0).2 (fun i => ts i.succ - ts 0) (Fin.tail zs)
      (fun i => hzs i.succ), doobFddDensity,
      doobFddDensity, fddDensity_succ, lastPoint_succ_tail z zs]
    have hc : h (zs 0) * (h (zs 0))⁻¹ = 1 := ENNReal.mul_inv_cancel (hzs 0).1 (hzs 0).2
    simp only [hTransform, div_eq_mul_inv]
    calc p (ts 0) z (zs 0) * h (zs 0) * (h z)⁻¹ *
          (fddDensity p (zs 0) (fun i => ts i.succ - ts 0) (Fin.tail zs) *
            (h (lastPoint (zs 0) (Fin.tail zs)) * (h (zs 0))⁻¹))
        = p (ts 0) z (zs 0) * fddDensity p (zs 0) (fun i => ts i.succ - ts 0) (Fin.tail zs) *
            (h (lastPoint (zs 0) (Fin.tail zs)) * (h z)⁻¹) * (h (zs 0) * (h (zs 0))⁻¹) := by
          ring
      _ = _ := by rw [hc, mul_one]

variable {μ : Measure E} [SigmaFinite μ]

/-- The telescoping holds `μ^k`-a.e. when `0 < h < ∞` μ-a.e. and at the start. -/
theorem ae_fddDensity_hTransform (hpos : ∀ᵐ y ∂μ, h y ≠ 0 ∧ h y ≠ ⊤) {z : E} (h0 : h z ≠ 0)
    (htop : h z ≠ ⊤) {k : ℕ} (ts : Fin k → ℝ) :
    ∀ᵐ zs ∂(Measure.pi fun _ : Fin k => μ),
      fddDensity (hTransform p h) z ts zs = doobFddDensity p h z ts zs := by
  have hall : ∀ᵐ zs ∂(Measure.pi fun _ : Fin k => μ), ∀ i, h (zs i) ≠ 0 ∧ h (zs i) ≠ ⊤ :=
    ae_all_iff.2 fun i =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => μ) (i := i)).eventually hpos
  filter_upwards [hall] with zs hzs
  exact fddDensity_hTransform h0 htop ts zs hzs

/-- **The finite-dimensional law of the `h`-transform** is `μ^k` with the killed density
`Πp · h(z_k)/h(z)`. -/
theorem fddMeasure_hTransform (hpos : ∀ᵐ y ∂μ, h y ≠ 0 ∧ h y ≠ ⊤) {z : E} (h0 : h z ≠ 0)
    (htop : h z ≠ ⊤) {k : ℕ} (ts : Fin k → ℝ) :
    fddMeasure μ (hTransform p h) z ts =
      (Measure.pi fun _ : Fin k => μ).withDensity (doobFddDensity p h z ts) :=
  withDensity_congr_ae (ae_fddDensity_hTransform hpos h0 htop ts)

/-- The killed density in integrated form: `∫⁻ F · Πp^h = ∫⁻ F · Πp · h(z_k)/h(z)`. -/
theorem lintegral_fddDensity_hTransform (hpos : ∀ᵐ y ∂μ, h y ≠ 0 ∧ h y ≠ ⊤) {z : E}
    (h0 : h z ≠ 0) (htop : h z ≠ ⊤) {k : ℕ} (ts : Fin k → ℝ) (F : (Fin k → E) → ℝ≥0∞) :
    ∫⁻ zs, F zs * fddDensity (hTransform p h) z ts zs ∂(Measure.pi fun _ : Fin k => μ) =
      ∫⁻ zs, F zs * doobFddDensity p h z ts zs ∂(Measure.pi fun _ : Fin k => μ) := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_fddDensity_hTransform hpos h0 htop ts] with zs hzs
  rw [hzs]

theorem measurable_doobFddDensity (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2)
    (hh : Measurable h) (z : E) {k : ℕ} (ts : Fin k → ℝ) :
    Measurable (doobFddDensity p h z ts) :=
  (measurable_fddDensity hp z ts).mul ((hh.comp (measurable_lastPoint z)).div_const _)

end Telescope

end BlockBand.Diffusion
