module

public import BlockBand.Diffusion.Process.BridgeProcess

/-!
# Chentsov moment bounds for bridges from kernel estimates

**Setting.** A measurable space `α` with a σ-finite reference measure `ν`, a transition density
`q : ℝ → α → α → ℝ≥0∞`, a start `z`, an end `e`, a duration `t > 0` with `0 < q t z e < ∞`,
and a "distance" `f : α → α → ℝ≥0∞` (in the application `f(a, b) = ‖b - a‖₄⁴`).

**Hypotheses** (`BrBridgeEstimates ν q f g z e t K G C F`, constants `K G C F : ℝ≥0`):
joint measurability of `q` and `f`; Chapman–Kolmogorov (in the form `ChapmanKolmogorov`); **symmetry**
`q h a b = q h b a` at all points; `f` symmetric with the weak triangle inequality
`f a c ≤ 8 (f a b + f b c)`; the **increment moment**
`∫ q_h(a, b) f(a, b) dν(b) ≤ K h² g(a)` for `0 < h ≤ t`, every `a`, with a measurable weight
`g ≥ 1`; the **weight moments** `∫ q_h(x, ·) g ≤ G` for `x ∈ {z, e}`, `0 < h ≤ t`, and
`g z, g e ≤ G`; the **on-diagonal bound** `q_h ≤ C` for `t/4 ≤ h ≤ t`; `f z e ≤ F`.

**Main statement** (`BrBridgeEstimates.bridgeMomentBound`). If moreover
`edist a b ^ p ≤ f a b` (pseudo-emetric `α`), then `BridgeMomentBound ν q z e t p 2 M` (the
Chentsov hypothesis of the bridge construction) for an explicit `M ≥ 0`.

**Proof.** With `S(u) = ∫ q_u(z, a) q_{t-u}(a, e) f(z, a) da`
(`(q_t(z,e))⁻¹ S(s)` is the start moment at time `s`):
* `t - u ≥ t/4`: bound `q_{t-u}(·, e) ≤ C` and use the increment moment: `S(u) ≤ CKG u²`;
* `t - u < t/4`: bound `q_u(z, ·) ≤ C`, split `f(z, a) ≤ 8(f(z, e) + f(e, a))`, use symmetry,
  the mass bound `∫ q_h(e, ·) ≤ G` and the increment moment from `e`: `S(u) ≤ 8C(FG + KGt²)`.
Interior two-point integral `B(r, s) = ∫∫ q_r(z,a) q_{s-r}(a,b) q_{t-s}(b,e) f(a,b)`:
* `t - s ≥ t/4`: as above (forward), `B ≤ CKG (s-r)²`;
* `r ≥ t/4`: bound `q_r(z, ·) ≤ C`, swap the integrals, use symmetry (reversal):
  `B ≤ CKG (s-r)²`;
* otherwise `s - r > t/2`: split `f(a, b) ≤ 8(f(z, a) + f(z, b))`, integrate out one node by
  Chapman–Kolmogorov: `B ≤ 8(S(r) + S(s))`, bounded.
The finish moment is the start moment of the reversed bridge (`BrBridgeEstimates.swap`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]

/-!
### One- and two-point bridge integrals
-/

section Formulas

variable {ν : Measure α} {q : ℝ → α → α → ℝ≥0∞}

/-- One-point bridge integrals. -/
theorem br_lintegral_bridgeFddMeasure_one (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2)
    {Φ : α → ℝ≥0∞} (hΦ : Measurable Φ) (z e : α) (t s : ℝ) :
    ∫⁻ zs, Φ (zs 0) ∂(bridgeFddMeasure ν q z e t ![s]) =
      (q t z e)⁻¹ * ∫⁻ a, q s z a * q (t - s) a e * Φ a ∂ν := by
  have hqr : ∀ h x, Measurable (q h x) := fun h x =>
    (hq h).comp (measurable_const.prodMk measurable_id)
  have hql : ∀ h y, Measurable fun a => q h a y := fun h y =>
    (hq h).comp (measurable_id.prodMk measurable_const)
  have hΦ1 : Measurable fun zs : Fin 1 → α => Φ (zs 0) := hΦ.comp (measurable_pi_apply 0)
  rw [bridgeFddMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_bridgeFddDensity hq z e t _) hΦ1]
  have mp := (measurePreserving_funUnique ν (Fin 1)).symm
  refine (mp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) _).symm.trans ?_
  have hm : Measurable fun a => q s z a * q (t - s) a e * Φ a :=
    ((hqr s z).mul (hql (t - s) e)).mul hΦ
  rw [← lintegral_const_mul _ hm]
  refine lintegral_congr fun a => ?_
  simp [bridgeFddDensity_eq, chainDensity_succ, bridgeWeight]
  ring

variable [SigmaFinite ν]

/-- Two-point bridge integrals. -/
theorem br_lintegral_bridgeFddMeasure_two (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2)
    {Φ : α → α → ℝ≥0∞} (hΦ : Measurable fun p : α × α => Φ p.1 p.2) (z e : α) (t r s : ℝ) :
    ∫⁻ zs, Φ (zs 0) (zs 1) ∂(bridgeFddMeasure ν q z e t ![r, s]) =
      (q t z e)⁻¹ * ∫⁻ a, ∫⁻ b, q r z a * q (s - r) a b * q (t - s) b e * Φ a b ∂ν ∂ν := by
  have hqr : ∀ h x, Measurable (q h x) := fun h x =>
    (hq h).comp (measurable_const.prodMk measurable_id)
  have hql : ∀ h y, Measurable fun a => q h a y := fun h y =>
    (hq h).comp (measurable_id.prodMk measurable_const)
  have hm : Measurable fun p : α × α => q r z p.1 * q (s - r) p.1 p.2 * q (t - s) p.2 e *
      Φ p.1 p.2 :=
    (((hqr r z).comp measurable_fst).mul (hq (s - r))).mul ((hql (t - s) e).comp measurable_snd)
      |>.mul hΦ
  have hΦ2 : Measurable fun zs : Fin 2 → α => Φ (zs 0) (zs 1) :=
    hΦ.comp (f := fun zs : Fin 2 → α => (zs 0, zs 1))
      ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
  rw [bridgeFddMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_bridgeFddDensity hq z e t _) hΦ2]
  have mp := (measurePreserving_finTwoArrow ν).symm
  have hm1 : ∀ a, Measurable fun b => q r z a * q (s - r) a b * q (t - s) b e * Φ a b :=
    fun a => hm.comp (f := fun b => (a, b)) (measurable_const.prodMk measurable_id)
  refine (mp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) _).symm.trans ?_
  rw [lintegral_prod _ ?_]
  · rw [← lintegral_const_mul _ hm.lintegral_prod_right']
    refine lintegral_congr fun a => ?_
    rw [← lintegral_const_mul _ (hm1 a)]
    refine lintegral_congr fun b => ?_
    simp [bridgeFddDensity_eq, chainDensity_succ, bridgeWeight]
    ring
  · exact ((measurable_bridgeFddDensity hq z e t _).mul hΦ2).comp
      (MeasurableEquiv.measurable _) |>.aemeasurable

/-- Additivity of iterated integrals. -/
theorem br_lintegral2_add {X Y : α → α → ℝ≥0∞} (hX : Measurable fun p : α × α => X p.1 p.2) :
    ∫⁻ a, ∫⁻ b, X a b + Y a b ∂ν ∂ν = ∫⁻ a, ∫⁻ b, X a b ∂ν ∂ν + ∫⁻ a, ∫⁻ b, Y a b ∂ν ∂ν := by
  have hXa : Measurable fun a => ∫⁻ b, X a b ∂ν := hX.lintegral_prod_right'
  rw [← lintegral_add_left hXa]
  refine lintegral_congr fun a => ?_
  have hXb : Measurable fun b => X a b := hX.comp (f := fun b => (a, b))
    (measurable_const.prodMk measurable_id)
  exact lintegral_add_left hXb _

end Formulas

/-!
### Elementary inequalities
-/

/-- `1 ≤ c · t⁻² · u²` when `t² ≤ c u²`. -/
theorem br_one_le_mul {c t u : ℝ} (hc : 0 ≤ c) (ht : 0 < t) (h : t ^ 2 ≤ c * u ^ 2) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal c * (ENNReal.ofReal (1 / t ^ 2) * ENNReal.ofReal (u ^ 2)) := by
  rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / t ^ 2 by positivity), ← ENNReal.ofReal_mul hc,
    ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : c * (1 / t ^ 2 * u ^ 2) = c * u ^ 2 / t ^ 2 := by field_simp
  rw [e, le_div_iff₀ (by positivity)]
  linarith

/-- Conversion of a finite constant to the real form of `BridgeMomentBound`. -/
theorem br_mul_ofReal_le {A : ℝ≥0∞} (hA : A ≠ ∞) {M x : ℝ} (hM : A.toReal ≤ M) (hx : 0 ≤ x) :
    A * ENNReal.ofReal x ≤ ENNReal.ofReal (M * x) := by
  rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hM hx)

/-!
### The estimates
-/

/-- **Kernel estimates for the bridge moment bound** (see the module docstring). -/
structure BrBridgeEstimates (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞) (f : α → α → ℝ≥0∞)
    (g : α → ℝ≥0∞) (z e : α) (t : ℝ) (K G C F : ℝ≥0) : Prop where
  meas_q : ∀ s, Measurable fun p : α × α => q s p.1 p.2
  ck : ChapmanKolmogorov ν q
  symm : ∀ h a b, q h a b = q h b a
  meas_f : Measurable fun p : α × α => f p.1 p.2
  f_symm : ∀ a b, f a b = f b a
  f_tri : ∀ a b c, f a c ≤ 8 * (f a b + f b c)
  meas_g : Measurable g
  incr : ∀ h, 0 < h → h ≤ t → ∀ a, ∫⁻ b, q h a b * f a b ∂ν ≤ K * ENNReal.ofReal (h ^ 2) * g a
  mom_z : ∀ h, 0 < h → h ≤ t → ∫⁻ a, q h z a * g a ∂ν ≤ G
  mom_e : ∀ h, 0 < h → h ≤ t → ∫⁻ a, q h e a * g a ∂ν ≤ G
  one_le_g : ∀ a, 1 ≤ g a
  g_z : g z ≤ G
  g_e : g e ≤ G
  diag : ∀ h, t / 4 ≤ h → h ≤ t → ∀ a b, q h a b ≤ C
  f_ze : f z e ≤ F

/-- The start integral `S(u) = ∫ q_u(z, a) q_{t-u}(a, e) f(z, a) dν(a)`. -/
def brS (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞) (f : α → α → ℝ≥0∞) (z e : α) (t u : ℝ) :
    ℝ≥0∞ :=
  ∫⁻ a, q u z a * q (t - u) a e * f z a ∂ν

/-- The interior integral `B(r, s) = ∫∫ q_r(z,a) q_{s-r}(a,b) q_{t-s}(b,e) f(a,b)`. -/
def brB (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞) (f : α → α → ℝ≥0∞) (z e : α) (t r s : ℝ) :
    ℝ≥0∞ :=
  ∫⁻ a, ∫⁻ b, q r z a * q (s - r) a b * q (t - s) b e * f a b ∂ν ∂ν

/-- The uniform bound `8C(FG + KGt²) + CKGt²` for `S`. -/
def brBs (t : ℝ) (K G C F : ℝ≥0) : ℝ≥0∞ :=
  C * K * G * ENNReal.ofReal (t ^ 2) + 8 * C * (F * G + K * G * ENNReal.ofReal (t ^ 2))

theorem brBs_ne_top (t : ℝ) (K G C F : ℝ≥0) : brBs t K G C F ≠ ∞ := by
  unfold brBs
  finiteness

namespace BrBridgeEstimates

variable {ν : Measure α} {q : ℝ → α → α → ℝ≥0∞} {f : α → α → ℝ≥0∞} {g : α → ℝ≥0∞} {z e : α}
  {t : ℝ} {K G C F : ℝ≥0}

/-- **Reversal**: the estimates are symmetric in the two endpoints. -/
theorem swap (H : BrBridgeEstimates ν q f g z e t K G C F) :
    BrBridgeEstimates ν q f g e z t K G C F :=
  { H with
    mom_z := H.mom_e
    mom_e := H.mom_z
    g_z := H.g_e
    g_e := H.g_z
    f_ze := by rw [H.f_symm]; exact H.f_ze }

variable (H : BrBridgeEstimates ν q f g z e t K G C F)
include H

theorem meas_right (h : ℝ) (x : α) : Measurable (q h x) :=
  (H.meas_q h).comp (measurable_const.prodMk measurable_id)

theorem meas_left (h : ℝ) (y : α) : Measurable fun a => q h a y :=
  (H.meas_q h).comp (measurable_id.prodMk measurable_const)

theorem meas_f_right (x : α) : Measurable (f x) :=
  H.meas_f.comp (measurable_const.prodMk measurable_id)

theorem mass_e {h : ℝ} (h0 : 0 < h) (ht : h ≤ t) : ∫⁻ a, q h e a ∂ν ≤ G :=
  (lintegral_mono fun a => le_mul_of_one_le_right' (H.one_le_g a)).trans (H.mom_e h h0 ht)

/-- `S(u) ≤ CKG u²` when `t - u ≥ t/4`. -/
theorem brS_le_small {u : ℝ} (hu : 0 < u) (hut : u ≤ t) (h4 : t / 4 ≤ t - u) :
    brS ν q f z e t u ≤ C * K * G * ENNReal.ofReal (u ^ 2) := by
  unfold brS
  calc ∫⁻ a, q u z a * q (t - u) a e * f z a ∂ν
      ≤ ∫⁻ a, C * (q u z a * f z a) ∂ν := by
        refine lintegral_mono fun a => ?_
        calc q u z a * q (t - u) a e * f z a ≤ q u z a * C * f z a := by
              gcongr
              exact H.diag _ h4 (by linarith) a e
          _ = C * (q u z a * f z a) := by ring
    _ = C * ∫⁻ a, q u z a * f z a ∂ν :=
        lintegral_const_mul _ ((H.meas_right u z).mul (H.meas_f_right z))
    _ ≤ C * (K * ENNReal.ofReal (u ^ 2) * g z) := by
        gcongr
        exact H.incr u hu hut z
    _ ≤ C * (K * ENNReal.ofReal (u ^ 2) * G) := by
        gcongr
        exact H.g_z
    _ = C * K * G * ENNReal.ofReal (u ^ 2) := by ring

/-- `S(u) ≤ 8C(FG + KGt²)` when `t - u < t/4`. -/
theorem brS_le_big {u : ℝ} (hut : u < t) (h4 : t - u < t / 4) :
    brS ν q f z e t u ≤ 8 * C * (F * G + K * G * ENNReal.ofReal (t ^ 2)) := by
  have hu4 : t / 4 ≤ u := by linarith
  have htu : 0 < t - u := by linarith
  have hpt : ∀ a, q u z a * q (t - u) a e * f z a ≤
      C * (8 * F * q (t - u) e a + 8 * (q (t - u) e a * f e a)) := by
    intro a
    have hf : f z a ≤ 8 * (F + f e a) :=
      (H.f_tri z e a).trans (by gcongr; exact H.f_ze)
    rw [H.symm (t - u) a e]
    calc q u z a * q (t - u) e a * f z a ≤ C * q (t - u) e a * (8 * (F + f e a)) := by
          gcongr ?_ * _ * ?_
          exact H.diag u hu4 hut.le z a
      _ = C * (8 * F * q (t - u) e a + 8 * (q (t - u) e a * f e a)) := by ring
  have hm1 : Measurable fun a => q (t - u) e a := H.meas_right (t - u) e
  have hm2 : Measurable fun a => q (t - u) e a * f e a := hm1.mul (H.meas_f_right e)
  have hm3 : Measurable fun a => 8 * (F : ℝ≥0∞) * q (t - u) e a := hm1.const_mul _
  have hm4 : Measurable fun a => 8 * (F : ℝ≥0∞) * q (t - u) e a +
      8 * (q (t - u) e a * f e a) := hm3.add (hm2.const_mul _)
  unfold brS
  calc ∫⁻ a, q u z a * q (t - u) a e * f z a ∂ν
      ≤ ∫⁻ a, C * (8 * F * q (t - u) e a + 8 * (q (t - u) e a * f e a)) ∂ν :=
        lintegral_mono hpt
    _ = C * (8 * F * ∫⁻ a, q (t - u) e a ∂ν + 8 * ∫⁻ a, q (t - u) e a * f e a ∂ν) := by
        rw [lintegral_const_mul _ hm4, lintegral_add_left hm3,
          lintegral_const_mul _ hm1, lintegral_const_mul _ hm2]
    _ ≤ C * (8 * F * G + 8 * (K * ENNReal.ofReal ((t - u) ^ 2) * g e)) := by
        gcongr
        · exact H.mass_e htu (by linarith)
        · exact H.incr (t - u) htu (by linarith) e
    _ ≤ C * (8 * F * G + 8 * (K * ENNReal.ofReal (t ^ 2) * G)) := by
        gcongr
        · linarith
        · exact H.g_e
    _ = 8 * C * (F * G + K * G * ENNReal.ofReal (t ^ 2)) := by ring

/-- `S(u)` is bounded on `(0, t)`. -/
theorem brS_le_Bs {u : ℝ} (hu : 0 < u) (hut : u < t) : brS ν q f z e t u ≤ brBs t K G C F := by
  by_cases h4 : t / 4 ≤ t - u
  · refine (H.brS_le_small hu hut.le h4).trans ?_
    refine le_trans ?_ le_self_add
    gcongr
  · exact (H.brS_le_big hut (not_le.1 h4)).trans le_add_self

/-- **Start moment**: `S(u) ≤ (CKG + 16 Bs t⁻²) u²` on `(0, t)`. -/
theorem brS_le {u : ℝ} (hu : 0 < u) (hut : u < t) :
    brS ν q f z e t u ≤
      (C * K * G + 16 * brBs t K G C F * ENNReal.ofReal (1 / t ^ 2)) * ENNReal.ofReal (u ^ 2) := by
  have ht : 0 < t := hu.trans hut
  by_cases h4 : t / 4 ≤ t - u
  · refine (H.brS_le_small hu hut.le h4).trans ?_
    gcongr
    exact le_self_add
  · have h1 := br_one_le_mul (c := 16) (u := u) (by norm_num) ht (by nlinarith)
    rw [ENNReal.ofReal_ofNat] at h1
    calc brS ν q f z e t u ≤ brBs t K G C F * 1 := by rw [mul_one]; exact H.brS_le_Bs hu hut
      _ ≤ brBs t K G C F * (16 * (ENNReal.ofReal (1 / t ^ 2) * ENNReal.ofReal (u ^ 2))) := by
          gcongr
      _ = 16 * brBs t K G C F * ENNReal.ofReal (1 / t ^ 2) * ENNReal.ofReal (u ^ 2) := by ring
      _ ≤ (C * K * G + 16 * brBs t K G C F * ENNReal.ofReal (1 / t ^ 2)) *
          ENNReal.ofReal (u ^ 2) := by
          rw [add_mul]
          exact le_add_self

/-- Interior, forward case `t - s ≥ t/4`. -/
theorem brB_le_fwd {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hst : s < t) (h4 : t / 4 ≤ t - s) :
    brB ν q f z e t r s ≤ C * K * G * ENNReal.ofReal ((s - r) ^ 2) := by
  unfold brB
  calc ∫⁻ a, ∫⁻ b, q r z a * q (s - r) a b * q (t - s) b e * f a b ∂ν ∂ν
      ≤ ∫⁻ a, ∫⁻ b, q r z a * C * (q (s - r) a b * f a b) ∂ν ∂ν := by
        refine lintegral_mono fun a => lintegral_mono fun b => ?_
        calc q r z a * q (s - r) a b * q (t - s) b e * f a b ≤
            q r z a * q (s - r) a b * C * f a b := by
              gcongr
              exact H.diag _ h4 (by linarith) b e
          _ = q r z a * C * (q (s - r) a b * f a b) := by ring
    _ = ∫⁻ a, q r z a * C * ∫⁻ b, q (s - r) a b * f a b ∂ν ∂ν :=
        lintegral_congr fun a =>
          lintegral_const_mul _ ((H.meas_right _ a).mul (H.meas_f_right a))
    _ ≤ ∫⁻ a, q r z a * C * (K * ENNReal.ofReal ((s - r) ^ 2) * g a) ∂ν := by
        refine lintegral_mono fun a => ?_
        gcongr
        exact H.incr _ (by linarith) (by linarith) a
    _ = C * K * ENNReal.ofReal ((s - r) ^ 2) * ∫⁻ a, q r z a * g a ∂ν := by
        have hm : Measurable fun a => q r z a * g a := (H.meas_right r z).mul H.meas_g
        rw [← lintegral_const_mul _ hm]
        refine lintegral_congr fun a => ?_
        ring
    _ ≤ C * K * ENNReal.ofReal ((s - r) ^ 2) * G := by
        gcongr
        exact H.mom_z r hr (by linarith)
    _ = C * K * G * ENNReal.ofReal ((s - r) ^ 2) := by ring

/-- Interior, backward case `r ≥ t/4` (reversal). -/
theorem brB_le_bwd [SFinite ν] {r s : ℝ} (hrs : r < s) (hst : s < t) (h4 : t / 4 ≤ r) :
    brB ν q f z e t r s ≤ C * K * G * ENNReal.ofReal ((s - r) ^ 2) := by
  have hsr : 0 < s - r := by linarith
  have hts : 0 < t - s := by linarith
  have hm : Measurable fun p : α × α =>
      (C : ℝ≥0∞) * (q (t - s) e p.2 * (q (s - r) p.2 p.1 * f p.2 p.1)) :=
    measurable_const.mul (((H.meas_right _ e).comp measurable_snd).mul
      (((H.meas_q _).comp measurable_swap).mul (H.meas_f.comp measurable_swap)))
  unfold brB
  calc ∫⁻ a, ∫⁻ b, q r z a * q (s - r) a b * q (t - s) b e * f a b ∂ν ∂ν
      ≤ ∫⁻ a, ∫⁻ b, C * (q (t - s) e b * (q (s - r) b a * f b a)) ∂ν ∂ν := by
        refine lintegral_mono fun a => lintegral_mono fun b => ?_
        rw [H.symm (s - r) a b, H.symm (t - s) b e, H.f_symm a b]
        calc q r z a * q (s - r) b a * q (t - s) e b * f b a ≤
            C * q (s - r) b a * q (t - s) e b * f b a := by
              gcongr
              exact H.diag r h4 (by linarith) z a
          _ = C * (q (t - s) e b * (q (s - r) b a * f b a)) := by ring
    _ = ∫⁻ b, ∫⁻ a, C * (q (t - s) e b * (q (s - r) b a * f b a)) ∂ν ∂ν :=
        lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ b, C * (q (t - s) e b * ∫⁻ a, q (s - r) b a * f b a ∂ν) ∂ν := by
        refine lintegral_congr fun b => ?_
        have h1 : Measurable fun a => q (s - r) b a * f b a :=
          (H.meas_right _ b).mul (H.meas_f_right b)
        rw [lintegral_const_mul _ (h1.const_mul _), lintegral_const_mul _ h1]
    _ ≤ ∫⁻ b, C * (q (t - s) e b * (K * ENNReal.ofReal ((s - r) ^ 2) * g b)) ∂ν := by
        refine lintegral_mono fun b => ?_
        gcongr
        exact H.incr _ hsr (by linarith) b
    _ = C * K * ENNReal.ofReal ((s - r) ^ 2) * ∫⁻ b, q (t - s) e b * g b ∂ν := by
        have hm : Measurable fun b => q (t - s) e b * g b := (H.meas_right _ e).mul H.meas_g
        rw [← lintegral_const_mul _ hm]
        refine lintegral_congr fun b => ?_
        ring
    _ ≤ C * K * ENNReal.ofReal ((s - r) ^ 2) * G := by
        gcongr
        exact H.mom_e _ hts (by linarith)
    _ = C * K * G * ENNReal.ofReal ((s - r) ^ 2) := by ring

/-- Interior, middle case: `B(r, s) ≤ 8 (S(r) + S(s))` for `0 < r < s < t`. -/
theorem brB_le_mid [SigmaFinite ν] {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hst : s < t) :
    brB ν q f z e t r s ≤ 8 * (brS ν q f z e t r + brS ν q f z e t s) := by
  have hsr : 0 < s - r := by linarith
  have hts : 0 < t - s := by linarith
  set X : α → α → ℝ≥0∞ := fun a b => 8 * (q r z a * f z a * (q (s - r) a b * q (t - s) b e))
    with hXdef
  set Y : α → α → ℝ≥0∞ := fun a b => 8 * (q r z a * q (s - r) a b * (q (t - s) b e * f z b))
    with hYdef
  have hX : Measurable fun p : α × α => X p.1 p.2 :=
    measurable_const.mul ((((H.meas_right r z).comp measurable_fst).mul
      ((H.meas_f_right z).comp measurable_fst)).mul
      ((H.meas_q (s - r)).mul ((H.meas_left (t - s) e).comp measurable_snd)))
  have hY : Measurable fun p : α × α => Y p.1 p.2 :=
    measurable_const.mul ((((H.meas_right r z).comp measurable_fst).mul (H.meas_q (s - r))).mul
      (((H.meas_left (t - s) e).comp measurable_snd).mul
        ((H.meas_f_right z).comp measurable_snd)))
  have eX : ∫⁻ a, ∫⁻ b, X a b ∂ν ∂ν = 8 * brS ν q f z e t r := by
    unfold brS
    have hm : Measurable fun a => q r z a * q (t - r) a e * f z a :=
      ((H.meas_right r z).mul (H.meas_left (t - r) e)).mul (H.meas_f_right z)
    rw [← lintegral_const_mul _ hm]
    refine lintegral_congr fun a => ?_
    simp only [hXdef]
    have h1 : Measurable fun b => q (s - r) a b * q (t - s) b e :=
      (H.meas_right _ a).mul (H.meas_left _ e)
    rw [lintegral_const_mul _ ((h1.const_mul _)), lintegral_const_mul _ h1,
      H.ck _ _ hsr hts, show s - r + (t - s) = t - r by ring]
    ring
  have eY : ∫⁻ a, ∫⁻ b, Y a b ∂ν ∂ν = 8 * brS ν q f z e t s := by
    rw [lintegral_lintegral_swap hY.aemeasurable]
    unfold brS
    have hm : Measurable fun a => q s z a * q (t - s) a e * f z a :=
      ((H.meas_right s z).mul (H.meas_left (t - s) e)).mul (H.meas_f_right z)
    rw [← lintegral_const_mul _ hm]
    refine lintegral_congr fun b => ?_
    simp only [hYdef]
    have h1 : Measurable fun a => q r z a * q (s - r) a b :=
      (H.meas_right _ z).mul (H.meas_left _ b)
    have e1 : ∫⁻ a, 8 * (q r z a * q (s - r) a b * (q (t - s) b e * f z b)) ∂ν =
        8 * ((∫⁻ a, q r z a * q (s - r) a b ∂ν) * (q (t - s) b e * f z b)) := by
      rw [← lintegral_mul_const _ h1, ← lintegral_const_mul _ (h1.mul_const _)]
    rw [e1, H.ck _ _ hr hsr, show r + (s - r) = s by ring]
    ring
  unfold brB
  calc ∫⁻ a, ∫⁻ b, q r z a * q (s - r) a b * q (t - s) b e * f a b ∂ν ∂ν
      ≤ ∫⁻ a, ∫⁻ b, X a b + Y a b ∂ν ∂ν := by
        refine lintegral_mono fun a => lintegral_mono fun b => ?_
        have hf : f a b ≤ 8 * (f z a + f z b) := by
          rw [H.f_symm z a]
          exact H.f_tri a z b
        calc q r z a * q (s - r) a b * q (t - s) b e * f a b ≤
            q r z a * q (s - r) a b * q (t - s) b e * (8 * (f z a + f z b)) := by gcongr
          _ = X a b + Y a b := by simp only [hXdef, hYdef]; ring
    _ = 8 * brS ν q f z e t r + 8 * brS ν q f z e t s := by rw [br_lintegral2_add hX, eX, eY]
    _ = 8 * (brS ν q f z e t r + brS ν q f z e t s) := by ring

/-- **Interior moment**: `B(r, s) ≤ (CKG + 64 Bs t⁻²)(s - r)²` for `0 < r < s < t`. -/
theorem brB_le [SigmaFinite ν] {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hst : s < t) :
    brB ν q f z e t r s ≤
      (C * K * G + 64 * brBs t K G C F * ENNReal.ofReal (1 / t ^ 2)) *
        ENNReal.ofReal ((s - r) ^ 2) := by
  have ht : 0 < t := hr.trans (hrs.trans hst)
  by_cases h1 : t / 4 ≤ t - s
  · refine (H.brB_le_fwd hr hrs hst h1).trans ?_
    gcongr
    exact le_self_add
  by_cases h2 : t / 4 ≤ r
  · refine (H.brB_le_bwd hrs hst h2).trans ?_
    gcongr
    exact le_self_add
  have h3 := br_one_le_mul (c := 4) (u := s - r) (by norm_num) ht (by nlinarith)
  rw [ENNReal.ofReal_ofNat] at h3
  calc brB ν q f z e t r s ≤ 8 * (brS ν q f z e t r + brS ν q f z e t s) := H.brB_le_mid hr hrs hst
    _ ≤ 8 * (brBs t K G C F + brBs t K G C F) := by
        gcongr
        · exact H.brS_le_Bs hr (hrs.trans hst)
        · exact H.brS_le_Bs (hr.trans hrs) hst
    _ = 16 * brBs t K G C F * 1 := by ring
    _ ≤ 16 * brBs t K G C F *
        (4 * (ENNReal.ofReal (1 / t ^ 2) * ENNReal.ofReal ((s - r) ^ 2))) := by
        gcongr
    _ = 64 * brBs t K G C F * ENNReal.ofReal (1 / t ^ 2) * ENNReal.ofReal ((s - r) ^ 2) := by ring
    _ ≤ _ := by
        rw [add_mul]
        exact le_add_self

/-- **Bridge moment bound from the kernel estimates**: `BridgeMomentBound ν q z e t p 2 M` for an
explicit `M`, when `edist a b ^ p ≤ f a b`. -/
theorem bridgeMomentBound [PseudoEMetricSpace α] [SigmaFinite ν] (ht : 0 < t)
    (h0 : q t z e ≠ 0) {p : ℝ} (hf : ∀ a b, edist a b ^ p ≤ f a b) :
    ∃ M : ℝ, 0 ≤ M ∧ BridgeMomentBound ν q z e t p 2 M := by
  set T4 := ENNReal.ofReal (1 / t ^ 2) with hT4
  set Aint := (C * K * G + 64 * brBs t K G C F * T4) * (q t z e)⁻¹ with hAint
  set Aend := (F : ℝ≥0∞) * T4 with hAend
  have hAint_top : Aint ≠ ∞ :=
    ENNReal.mul_ne_top (by have := brBs_ne_top t K G C F; finiteness) (ENNReal.inv_ne_top.2 h0)
  have hAend_top : Aend ≠ ∞ := by finiteness
  set M := Aint.toReal + Aend.toReal with hM
  have hM1 : Aint.toReal ≤ M := le_add_of_nonneg_right ENNReal.toReal_nonneg
  have hM2 : Aend.toReal ≤ M := le_add_of_nonneg_left ENNReal.toReal_nonneg
  have hstart : ∀ u, 0 < u → u < t → (q t z e)⁻¹ * brS ν q f z e t u ≤
      Aint * ENNReal.ofReal (u ^ 2) := by
    intro u hu hut
    calc (q t z e)⁻¹ * brS ν q f z e t u ≤ (q t z e)⁻¹ *
        ((C * K * G + 16 * brBs t K G C F * T4) * ENNReal.ofReal (u ^ 2)) := by
          gcongr
          exact H.brS_le hu hut
      _ ≤ (q t z e)⁻¹ *
          ((C * K * G + 64 * brBs t K G C F * T4) * ENNReal.ofReal (u ^ 2)) := by
          gcongr
          norm_num
      _ = Aint * ENNReal.ofReal (u ^ 2) := by rw [hAint]; ring
  refine ⟨M, add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro r s hr hrs hst
    rw [Real.rpow_two]
    calc ∫⁻ zs, edist (zs 0) (zs 1) ^ p ∂(bridgeFddMeasure ν q z e t ![r, s])
        ≤ ∫⁻ zs, f (zs 0) (zs 1) ∂(bridgeFddMeasure ν q z e t ![r, s]) :=
          lintegral_mono fun zs => hf _ _
      _ = (q t z e)⁻¹ * brB ν q f z e t r s :=
          br_lintegral_bridgeFddMeasure_two H.meas_q H.meas_f z e t r s
      _ ≤ (q t z e)⁻¹ * ((C * K * G + 64 * brBs t K G C F * T4) *
          ENNReal.ofReal ((s - r) ^ 2)) := by
          gcongr
          exact H.brB_le hr hrs hst
      _ = Aint * ENNReal.ofReal ((s - r) ^ 2) := by rw [hAint]; ring
      _ ≤ ENNReal.ofReal (M * (s - r) ^ 2) := br_mul_ofReal_le hAint_top hM1 (by positivity)
  · intro s hs hst
    rw [Real.rpow_two]
    calc ∫⁻ zs, edist z (zs 0) ^ p ∂(bridgeFddMeasure ν q z e t ![s])
        ≤ ∫⁻ zs, f z (zs 0) ∂(bridgeFddMeasure ν q z e t ![s]) :=
          lintegral_mono fun zs => hf _ _
      _ = (q t z e)⁻¹ * brS ν q f z e t s :=
          br_lintegral_bridgeFddMeasure_one H.meas_q (H.meas_f_right z) z e t s
      _ ≤ Aint * ENNReal.ofReal (s ^ 2) := hstart s hs hst
      _ ≤ ENNReal.ofReal (M * s ^ 2) := br_mul_ofReal_le hAint_top hM1 (by positivity)
  · intro s hs hst
    rw [Real.rpow_two]
    have hfin : ∀ u, 0 < u → u < t → (q t e z)⁻¹ * brS ν q f e z t u ≤
        Aint * ENNReal.ofReal (u ^ 2) := by
      intro u hu hut
      calc (q t e z)⁻¹ * brS ν q f e z t u ≤ (q t e z)⁻¹ *
          ((C * K * G + 16 * brBs t K G C F * T4) * ENNReal.ofReal (u ^ 2)) := by
            gcongr
            exact H.swap.brS_le hu hut
        _ ≤ (q t e z)⁻¹ *
            ((C * K * G + 64 * brBs t K G C F * T4) * ENNReal.ofReal (u ^ 2)) := by
            gcongr
            norm_num
        _ = Aint * ENNReal.ofReal (u ^ 2) := by rw [hAint, H.symm t e z]; ring
    have hrev : brS ν q f e z t (t - s) = ∫⁻ a, q s z a * q (t - s) a e * f a e ∂ν := by
      unfold brS
      refine lintegral_congr fun a => ?_
      rw [show t - (t - s) = s by ring, H.symm s a z, H.symm (t - s) e a, H.f_symm e a]
      ring
    calc ∫⁻ zs, edist (zs 0) e ^ p ∂(bridgeFddMeasure ν q z e t ![s])
        ≤ ∫⁻ zs, f (zs 0) e ∂(bridgeFddMeasure ν q z e t ![s]) :=
          lintegral_mono fun zs => hf _ _
      _ = (q t z e)⁻¹ * ∫⁻ a, q s z a * q (t - s) a e * f a e ∂ν :=
          br_lintegral_bridgeFddMeasure_one H.meas_q
            (H.meas_f.comp (measurable_id.prodMk measurable_const)) z e t s
      _ = (q t e z)⁻¹ * brS ν q f e z t (t - s) := by rw [hrev, H.symm t e z]
      _ ≤ Aint * ENNReal.ofReal ((t - s) ^ 2) := hfin (t - s) (by linarith) (by linarith)
      _ ≤ ENNReal.ofReal (M * (t - s) ^ 2) := br_mul_ofReal_le hAint_top hM1 (by positivity)
  · rw [Real.rpow_two]
    have h1 : T4 * ENNReal.ofReal (t ^ 2) = 1 := by
      rw [hT4, ← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ (by positivity),
        ENNReal.ofReal_one]
    calc edist z e ^ p ≤ f z e := hf z e
      _ ≤ F := H.f_ze
      _ = Aend * ENNReal.ofReal (t ^ 2) := by rw [hAend, mul_assoc, h1, mul_one]
      _ ≤ ENNReal.ofReal (M * t ^ 2) := br_mul_ofReal_le hAend_top hM2 (by positivity)

end BrBridgeEstimates

end BlockBand.Diffusion
