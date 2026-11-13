module

public import BlockBand.Diffusion.Markov.HTransform
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Doob `h`-transform identification at the finite-dimensional level

A process `Z : ℝ → Ω → E` with lifetime `ζ : Ω → ℝ≥0∞` on a measure space `(Ω, P)` has **the
killed law of the `h`-transform of `p` from `z`** (`IsDoobKilledLaw μ p h z P Z ζ`) if for all
`0 < t₁ < ⋯ < t_k` (`t₀ = 0`) and measurable `F ≥ 0`,
`E[F(Z_{t₁}, …, Z_{t_k}); t_k < ζ] = ∫⁻ F · Πp(ts) · h(z_k)/h(z) dμ^k`
(the event includes `ζ = ∞`; at `k = 0` it says `P(0 < ζ) = 1` when `0 < h(z) < ∞`). This is the
generic form of `LbkDoobKilledLaw` (`p = ofReal ∘ lbkKernel`, `h = ofReal ∘ lbkHarm`, since
`(x + y) H(z_k) = H(z_k)/H(z)`).

**Proved here.**
* (a) `doobKilledLaw_survival`, `doobKilledLaw_measure_survival`: `P(t < ζ) = P_t h(z)/h(z)`;
  `doobKilledLaw_pos`, `doobKilledLaw_ae_pos`: `P(0 < ζ) = 1`, so `ζ > 0` a.s.
* (b1) `doobKilledLaw_lifetime_cdf`, `doobKilledLaw_lifetime_law`: given a **lifetime-density
  identity** at `z`, `P_t h(z) + ∫_{(0,t]} q_s(z) ds = h(z)` for `t > 0` (the additive form of
  `h - P_t h = ∫_0^t q_s ds`, generic form of `LbkCornerHeatIdentity`), the lifetime law on
  `{ζ < ∞}` is `q_s(z)/h(z) ds` on `(0, ∞)`: `E[g(ζ); ζ < ∞] = ∫_{(0,∞)} g(s) q_s(z)/h(z) ds`.
* (b2) `doobKilledLaw_joint_law`: given in addition the **Markov property of the lifetime at `t_k`**
  (`IsLifetimeMarkovAt`, generic form of `LbkLifetimeMarkov`) with the lifetime functional
  `Λ(w) = ∫_{(0,∞)} g(t_k + s) q_s(w)/h(w) ds` (which (b1) identifies as the lifetime functional
  of every realization from `w`), the joint law of path and lifetime:
  `E[g(ζ) F(Z_{t₁..t_k}); t_k < ζ < ∞] =
    h(z)⁻¹ ∫⁻ F(zs) Πp(ts)(zs) ∫_{(0,∞)} g(t_k + s) q_s(z_k) ds dμ^k(zs)`
  (the factors `h(z_k)` telescope). This mirrors `lbkHTransformLaw_of_split`.

The bridge disintegration of the right side ("conditionally on `ζ = t` the path is the
`p`-bridge to the absorbing point") is in `BlockBand.Diffusion.Markov.Bridge`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] {Ω : Type*} [MeasurableSpace Ω]

/-!
### Definitions
-/

/-- **The killed finite-dimensional law of the `h`-transform** of `p` (relative to `μ`) from `z`,
for the process `Z` with lifetime `ζ` under `P`. -/
def IsDoobKilledLaw (μ : Measure E) (p : ℝ → E → E → ℝ≥0∞) (h : E → ℝ≥0∞) (z : E)
    (P : Measure Ω) (Z : ℝ → Ω → E) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∀ (k : ℕ) (ts : Fin k → ℝ), StrictMono ts → (∀ i, 0 < ts i) →
    ∀ F : (Fin k → E) → ℝ≥0∞, Measurable F →
      ∫⁻ ω, (if ENNReal.ofReal (lastTime ts) < ζ ω then F (fun i => Z (ts i) ω) else 0) ∂P =
        ∫⁻ zs, F zs * doobFddDensity p h z ts zs ∂(Measure.pi fun _ : Fin k => μ)

/-- The lifetime functional `Λ_g(w) = ∫_{(0,∞)} g(s) q_s(w)/h(w) ds` of a lifetime density
`q_s(w)/h(w)` from `w`. -/
def lifetimeFunctional (q : ℝ → E → ℝ≥0∞) (h : E → ℝ≥0∞) (g : ℝ → ℝ≥0∞) (w : E) : ℝ≥0∞ :=
  ∫⁻ s in Ioi 0, g s * (q s w / h w)

/-- **The Markov property of the lifetime at the last time `t_k`**, for the function `g` and the
lifetime functional `Λ`: `E[G(Z_{t₁..t_k}) g(ζ - t_k); t_k < ζ < ∞] =
E[G(Z_{t₁..t_k}) Λ(Z_{t_k}); t_k < ζ]` (with `Z_{t₀} = z`) for all measurable `G ≥ 0`. -/
def IsLifetimeMarkovAt (P : Measure Ω) (Z : ℝ → Ω → E) (ζ : Ω → ℝ≥0∞) (z : E) {k : ℕ}
    (ts : Fin k → ℝ) (g : ℝ → ℝ≥0∞) (Λ : E → ℝ≥0∞) : Prop :=
  ∀ G : (Fin k → E) → ℝ≥0∞, Measurable G →
    ∫⁻ ω, (if ζ ω < ⊤ ∧ ENNReal.ofReal (lastTime ts) < ζ ω
        then G (fun i => Z (ts i) ω) * g ((ζ ω).toReal - lastTime ts) else 0) ∂P =
      ∫⁻ ω, (if ENNReal.ofReal (lastTime ts) < ζ ω
        then G (fun i => Z (ts i) ω) * Λ (lastPoint z fun i => Z (ts i) ω) else 0) ∂P

/-!
### Elementary facts
-/

theorem lintegral_ite_one {P : Measure Ω} {q : Ω → Prop} [DecidablePred q]
    (hq : MeasurableSet {ω | q ω}) : ∫⁻ ω, (if q ω then (1 : ℝ≥0∞) else 0) ∂P = P {ω | q ω} := by
  rw [← lintegral_indicator_one hq]
  refine lintegral_congr fun ω => ?_
  by_cases h : q ω <;> simp [h]

/-- On `{ζ > 0}`, `{tᵢ < ζ ∀ i} = {t_k < ζ}`. -/
theorem forall_ofReal_lt_iff {k : ℕ} {ts : Fin k → ℝ} (hts : StrictMono ts) {σ : ℝ≥0∞}
    (hσ : 0 < σ) : (∀ i, ENNReal.ofReal (ts i) < σ) ↔ ENNReal.ofReal (lastTime ts) < σ := by
  cases k with
  | zero => simp [lastTime_zero, hσ]
  | succ m =>
    rw [lastTime_succ]
    exact ⟨fun h => h _, fun h i =>
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (hts.monotone (Fin.le_last i))) h⟩

theorem measurable_lifetimeFunctional {q : ℝ → E → ℝ≥0∞}
    (hq : Measurable fun w : ℝ × E => q w.1 w.2) {h : E → ℝ≥0∞} (hh : Measurable h)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) : Measurable (lifetimeFunctional q h g) := by
  have hf : Measurable fun x : E × ℝ => g x.2 * (q x.2 x.1 / h x.1) :=
    (hg.comp measurable_snd).mul ((hq.comp (measurable_snd.prodMk measurable_fst)).div
      (hh.comp measurable_fst))
  exact hf.lintegral_prod_right'

/-- The last point avoids a μ-null set `μ^k`-a.e. (and is `z` for `k = 0`). -/
theorem ae_lastPoint {μ : Measure E} [SigmaFinite μ] {r : E → Prop} (hr : ∀ᵐ y ∂μ, r y)
    {z : E} (hz : r z) {k : ℕ} :
    ∀ᵐ zs ∂(Measure.pi fun _ : Fin k => μ), r (lastPoint z zs) := by
  cases k with
  | zero => exact ae_of_all _ fun zs => hz
  | succ m =>
    have := (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (m + 1) => μ)
      (i := Fin.last m)).eventually hr
    filter_upwards [this] with zs hzs
    rw [lastPoint_succ]
    exact hzs

section Killed

variable {μ : Measure E} [SigmaFinite μ] {p : ℝ → E → E → ℝ≥0∞} {h : E → ℝ≥0∞} {z : E}
  {P : Measure Ω} {Z : ℝ → Ω → E} {ζ : Ω → ℝ≥0∞}

/-!
### (a) Survival
-/

/-- **`P(0 < ζ) = 1`** (the killed law at `k = 0`), in `if`-integral form. -/
theorem doobKilledLaw_pos (hK : IsDoobKilledLaw μ p h z P Z ζ) (h0 : h z ≠ 0) (htop : h z ≠ ⊤) :
    ∫⁻ ω, (if 0 < ζ ω then (1 : ℝ≥0∞) else 0) ∂P = 1 := by
  have := hK 0 (fun i => i.elim0) (fun a _ _ => a.elim0) (fun i => i.elim0) (fun _ => 1)
    measurable_const
  simp only [lastTime_zero, ENNReal.ofReal_zero] at this
  have h1 : ∀ zs : Fin 0 → E, 1 * doobFddDensity p h z (fun i => i.elim0) zs = 1 := by
    intro zs
    rw [one_mul, doobFddDensity, fddDensity_zero, one_mul, lastPoint_zero,
      ENNReal.div_self h0 htop]
  simp_rw [h1] at this
  rw [this, lintegral_const, Measure.pi_univ]
  simp

/-- **The survival probability** `P(t < ζ) = P_t h(z) / h(z)` (the killed law at `k = 1`,
`F = 1`), in `if`-integral form (no measurability of `ζ` needed). -/
theorem doobKilledLaw_survival (hK : IsDoobKilledLaw μ p h z P Z ζ)
    (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2) (hh : Measurable h) {t : ℝ}
    (ht : 0 < t) :
    ∫⁻ ω, (if ENNReal.ofReal t < ζ ω then (1 : ℝ≥0∞) else 0) ∂P =
      (∫⁻ b, p t z b * h b ∂μ) / h z := by
  have h1 := hK 1 ![t] (Subsingleton.strictMono _)
    (fun i => by simpa [Fin.fin_one_eq_zero i] using ht) (fun _ => 1) measurable_const
  have hlast : lastTime ![t] = t := by simp [lastTime_succ]
  rw [hlast] at h1
  rw [h1, lintegral_pi_one μ (f := fun zs => 1 * doobFddDensity p h z ![t] zs)
    (measurable_const.mul (measurable_doobFddDensity hp hh z _))]
  have hx : ∀ x, (1 : ℝ≥0∞) * doobFddDensity p h z ![t] (fun _ => x) =
      p t z x * h x * (h z)⁻¹ := by
    intro x
    rw [one_mul, doobFddDensity, fddDensity_succ, fddDensity_zero, lastPoint_succ]
    simp only [Matrix.cons_val_zero, mul_one, div_eq_mul_inv]
    ring
  simp_rw [hx]
  rw [lintegral_mul_const (f := fun x => p t z x * h x) _
    (((hp t).comp (measurable_const.prodMk measurable_id)).mul hh), div_eq_mul_inv]

/-- A measurable modification of the lifetime has the same `if`-integrals. -/
theorem lintegral_ite_congr_ae {ζ' : Ω → ℝ≥0∞} (hζ : ζ =ᵐ[P] ζ') {q : ℝ≥0∞ → Prop}
    [DecidablePred q] (f : Ω → ℝ≥0∞ → ℝ≥0∞) :
    ∫⁻ ω, (if q (ζ ω) then f ω (ζ ω) else 0) ∂P =
      ∫⁻ ω, (if q (ζ' ω) then f ω (ζ' ω) else 0) ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [hζ] with ω hω
  rw [hω]

/-- **The survival probability** `P(t < ζ) = P_t h(z)/h(z)`, for an a.e.-measurable lifetime. -/
theorem doobKilledLaw_measure_survival (hK : IsDoobKilledLaw μ p h z P Z ζ)
    (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2) (hh : Measurable h)
    (hζ : AEMeasurable ζ P) {t : ℝ} (ht : 0 < t) :
    P {ω | ENNReal.ofReal t < ζ ω} = (∫⁻ b, p t z b * h b ∂μ) / h z := by
  rw [← doobKilledLaw_survival hK hp hh ht,
    lintegral_ite_congr_ae hζ.ae_eq_mk (q := fun σ => ENNReal.ofReal t < σ) (fun _ _ => 1),
    lintegral_ite_one (measurableSet_lt measurable_const hζ.measurable_mk)]
  refine measure_congr ?_
  filter_upwards [hζ.ae_eq_mk] with ω hω
  simp [hω]

/-- **`P(0 < ζ) = 1`** for an a.e.-measurable lifetime. -/
theorem doobKilledLaw_measure_pos (hK : IsDoobKilledLaw μ p h z P Z ζ) (h0 : h z ≠ 0)
    (htop : h z ≠ ⊤) (hζ : AEMeasurable ζ P) : P {ω | 0 < ζ ω} = 1 := by
  rw [← doobKilledLaw_pos hK h0 htop,
    lintegral_ite_congr_ae hζ.ae_eq_mk (q := fun σ => 0 < σ) (fun _ _ => 1),
    lintegral_ite_one (measurableSet_lt measurable_const hζ.measurable_mk)]
  refine measure_congr ?_
  filter_upwards [hζ.ae_eq_mk] with ω hω
  simp [hω]

/-- **`ζ > 0` a.s.** under a probability measure. -/
theorem doobKilledLaw_ae_pos [IsProbabilityMeasure P] (hK : IsDoobKilledLaw μ p h z P Z ζ)
    (h0 : h z ≠ 0) (htop : h z ≠ ⊤) (hζ : AEMeasurable ζ P) : ∀ᵐ ω ∂P, 0 < ζ ω := by
  have hS : MeasurableSet {ω | 0 < hζ.mk ζ ω} := measurableSet_lt measurable_const hζ.measurable_mk
  have h1 : P {ω | 0 < hζ.mk ζ ω} = 1 := by
    rw [← doobKilledLaw_measure_pos hK h0 htop hζ]
    refine measure_congr ?_
    filter_upwards [hζ.ae_eq_mk] with ω hω
    simp [hω]
  have hc : P {ω | 0 < hζ.mk ζ ω}ᶜ = 0 := by rw [prob_compl_eq_one_sub hS, h1, tsub_self]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hc, hζ.ae_eq_mk] with ω h1 h2
  rw [h2]
  simpa [pos_iff_ne_zero] using h1

/-!
### The lifetime law
-/

/-- **The distribution function of the lifetime**: `P(ζ ≤ t) = (∫_{(0,t]} q_s(z) ds)/h(z)` for
`t > 0`, from the survival probability and the lifetime-density identity at `z`. -/
theorem doobKilledLaw_lifetime_cdf [IsProbabilityMeasure P] (hK : IsDoobKilledLaw μ p h z P Z ζ)
    (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2) (hh : Measurable h)
    (hζ : AEMeasurable ζ P) (h0 : h z ≠ 0) (htop : h z ≠ ⊤) {q : ℝ → E → ℝ≥0∞}
    (hheat : ∀ t, 0 < t → ∫⁻ b, p t z b * h b ∂μ + ∫⁻ s in Ioc 0 t, q s z = h z) {t : ℝ}
    (ht : 0 < t) :
    P {ω | ζ ω ≤ ENNReal.ofReal t} = (∫⁻ s in Ioc 0 t, q s z) / h z := by
  set A := ∫⁻ b, p t z b * h b ∂μ
  set B := ∫⁻ s in Ioc 0 t, q s z
  have hS0 : MeasurableSet {ω | hζ.mk ζ ω ≤ ENNReal.ofReal t} :=
    measurableSet_le hζ.measurable_mk measurable_const
  have hS : NullMeasurableSet {ω | ζ ω ≤ ENNReal.ofReal t} P :=
    hS0.nullMeasurableSet.congr (by
      filter_upwards [hζ.ae_eq_mk] with ω hω
      simp [hω])
  have hcompl : {ω | ζ ω ≤ ENNReal.ofReal t}ᶜ = {ω | ENNReal.ofReal t < ζ ω} := by
    ext ω
    simp
  have hsum := measure_add_measure_compl₀ hS
  rw [hcompl, doobKilledLaw_measure_survival hK hp hh hζ ht, measure_univ] at hsum
  have hone : A / h z + B / h z = 1 := by
    rw [← ENNReal.add_div, hheat t ht, ENNReal.div_self h0 htop]
  have hfin : A / h z ≠ ⊤ := by
    rw [← doobKilledLaw_measure_survival hK hp hh hζ ht]
    exact measure_ne_top P _
  rw [← hone, add_comm (A / h z)] at hsum
  exact (ENNReal.add_left_inj hfin).1 hsum

/-- **The lifetime law** on `{ζ < ∞}`: for measurable `g ≥ 0`,
`E[g(ζ); ζ < ∞] = ∫_{(0,∞)} g(s) q_s(z)/h(z) ds`, from the killed law (at `k = 0, 1`) and the
lifetime-density identity `P_t h(z) + ∫_{(0,t]} q_s(z) ds = h(z)` (`t > 0`). -/
theorem doobKilledLaw_lifetime_law [IsProbabilityMeasure P] (hK : IsDoobKilledLaw μ p h z P Z ζ)
    (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2) (hh : Measurable h)
    (hζ : AEMeasurable ζ P) (h0 : h z ≠ 0) (htop : h z ≠ ⊤) {q : ℝ → E → ℝ≥0∞}
    (hq : Measurable fun s => q s z)
    (hheat : ∀ t, 0 < t → ∫⁻ b, p t z b * h b ∂μ + ∫⁻ s in Ioc 0 t, q s z = h z)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, (if ζ ω < ⊤ then g (ζ ω).toReal else 0) ∂P =
      ∫⁻ s in Ioi 0, g s * (q s z / h z) := by
  set τ := hζ.mk ζ
  have hτm : Measurable τ := hζ.measurable_mk
  have hτ : ζ =ᵐ[P] τ := hζ.ae_eq_mk
  have hpos : ∀ᵐ ω ∂P, 0 < τ ω := by
    filter_upwards [doobKilledLaw_ae_pos hK h0 htop hζ, hτ] with ω h1 h2
    exact h2 ▸ h1
  set f : Ω → ℝ := fun ω => (τ ω).toReal with hf
  have hfm : Measurable f := hτm.ennreal_toReal
  set S : Set Ω := {ω | τ ω < ⊤} with hSdef
  have hS : MeasurableSet S := measurableSet_lt hτm measurable_const
  set dens : ℝ → ℝ≥0∞ := fun s => q s z / h z with hdens
  have hdm : Measurable dens := hq.div_const _
  set μ1 : Measure ℝ := (P.restrict S).map f with hμ1
  set ν : Measure ℝ := (volume.restrict (Ioi (0 : ℝ))).withDensity dens with hν
  have hcdf : ∀ r : ℝ, 0 < r → P {ω | τ ω ≤ ENNReal.ofReal r} = (∫⁻ s in Ioc 0 r, q s z) / h z := by
    intro r hr
    rw [← doobKilledLaw_lifetime_cdf hK hp hh hζ h0 htop hheat hr]
    refine measure_congr ?_
    filter_upwards [hτ] with ω hω
    simp [hω]
  have hμν : μ1 = ν := by
    refine Measure.ext_of_Iic μ1 ν fun r => ?_
    rw [hμ1, hν, Measure.map_apply hfm measurableSet_Iic,
      Measure.restrict_apply (hfm measurableSet_Iic),
      withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioi]
    rcases le_or_gt r 0 with hr | hr
    · rw [Ioc_eq_empty (not_lt.2 hr), Measure.restrict_empty, lintegral_zero_measure]
      rw [ae_iff] at hpos
      refine measure_mono_null (fun ω hω => ?_) hpos
      simp only [mem_inter_iff, mem_preimage, mem_Iic, hSdef, mem_ofPred_eq, hf] at hω
      simp only [mem_ofPred_eq, not_lt, nonpos_iff_eq_zero]
      have h0' : (τ ω).toReal = 0 := le_antisymm (hω.1.trans hr) ENNReal.toReal_nonneg
      rcases (ENNReal.toReal_eq_zero_iff _).1 h0' with h | h
      · exact h
      · exact absurd h hω.2.ne
    · have hset : f ⁻¹' Iic r ∩ S = {ω | τ ω ≤ ENNReal.ofReal r} := by
        ext ω
        simp only [mem_inter_iff, mem_preimage, mem_Iic, hSdef, mem_ofPred_eq, hf]
        constructor
        · rintro ⟨h1, h2⟩
          exact (ENNReal.le_ofReal_iff_toReal_le h2.ne hr.le).2 h1
        · intro h1
          have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
          exact ⟨(ENNReal.le_ofReal_iff_toReal_le hne hr.le).1 h1, lt_top_iff_ne_top.2 hne⟩
      rw [hset, hcdf r hr, hdens]
      simp only [div_eq_mul_inv]
      rw [lintegral_mul_const _ hq]
  have hL : ∫⁻ ω, (if ζ ω < ⊤ then g (ζ ω).toReal else 0) ∂P = ∫⁻ r, g r ∂μ1 := by
    rw [hμ1, lintegral_map hg hfm, ← lintegral_indicator hS]
    refine lintegral_congr_ae ?_
    filter_upwards [hτ] with ω hω
    simp only [indicator, hSdef, mem_ofPred_eq, hω, hf]
  rw [hL, hμν, hν, lintegral_withDensity_eq_lintegral_mul _ hdm hg]
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply, hdens]
  ring

/-!
### The joint law of path and lifetime
-/

/-- **The joint law of the path and the lifetime** of the `h`-transform (the abstract content of
`lbkHTransformLaw_of_split`): from the killed law and the Markov property of the lifetime at
`t_k` with the lifetime functional `Λ(w) = ∫_{(0,∞)} g(t_k + s) q_s(w)/h(w) ds`,
`E[g(ζ) F(Z_{t₁..t_k}); tᵢ < ζ ∀ i, ζ < ∞] =
  h(z)⁻¹ ∫⁻ F(zs) Πp(ts)(zs) ∫_{(0,∞)} g(t_k + s) q_s(z_k) ds dμ^k(zs)`. -/
theorem doobKilledLaw_joint_law [IsProbabilityMeasure P] (hK : IsDoobKilledLaw μ p h z P Z ζ)
    (hh : Measurable h) (hpos : ∀ᵐ y ∂μ, h y ≠ 0 ∧ h y ≠ ⊤) (hζ : AEMeasurable ζ P) (h0 : h z ≠ 0)
    (htop : h z ≠ ⊤) {q : ℝ → E → ℝ≥0∞} (hq : Measurable fun w : ℝ × E => q w.1 w.2) {k : ℕ}
    {ts : Fin k → ℝ} (hts : StrictMono ts) (htp : ∀ i, 0 < ts i) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g)
    (hM : IsLifetimeMarkovAt P Z ζ z ts (fun s => g (lastTime ts + s))
      (lifetimeFunctional q h fun s => g (lastTime ts + s)))
    {F : (Fin k → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, (if ζ ω < ⊤ ∧ ∀ i, ENNReal.ofReal (ts i) < ζ ω
        then g (ζ ω).toReal * F (fun i => Z (ts i) ω) else 0) ∂P =
      (h z)⁻¹ * ∫⁻ zs, F zs * fddDensity p z ts zs *
        (∫⁻ s in Ioi 0, g (lastTime ts + s) * q s (lastPoint z zs))
          ∂(Measure.pi fun _ : Fin k => μ) := by
  set T := lastTime ts with hT
  set Λ := lifetimeFunctional q h fun s => g (T + s) with hΛdef
  have hgT : Measurable fun s => g (T + s) := hg.comp (measurable_const.add measurable_id)
  have hΛm : Measurable Λ := measurable_lifetimeFunctional hq hh hgT
  -- Step 1: the event `{tᵢ < ζ ∀ i}` is `{t_k < ζ}` a.s., and `g(ζ) = g(T + (ζ - T))`.
  have hstep1 : ∫⁻ ω, (if ζ ω < ⊤ ∧ ∀ i, ENNReal.ofReal (ts i) < ζ ω
        then g (ζ ω).toReal * F (fun i => Z (ts i) ω) else 0) ∂P =
      ∫⁻ ω, (if ζ ω < ⊤ ∧ ENNReal.ofReal T < ζ ω
        then F (fun i => Z (ts i) ω) * g (T + ((ζ ω).toReal - T)) else 0) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [doobKilledLaw_ae_pos hK h0 htop hζ] with ω hω
    have he := forall_ofReal_lt_iff hts hω
    by_cases hc : ζ ω < ⊤ ∧ ENNReal.ofReal T < ζ ω
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hc.1, he.2 hc.2⟩),
        ite_eq_left_of_eq_true _ _ (eq_true hc), add_sub_cancel, mul_comm]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hc ⟨h.1, he.1 h.2⟩),
        ite_eq_right_of_eq_false _ _ (eq_false hc)]
  -- Step 2: the Markov property at `t_k`; Step 3: the killed law applied to `F(zs) Λ(z_k)`.
  have hFΛ : Measurable fun zs : Fin k → E => F zs * Λ (lastPoint z zs) :=
    hF.mul (hΛm.comp (measurable_lastPoint z))
  rw [hstep1, hM F hF, hK k ts hts htp _ hFΛ, ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 h0)]
  -- Step 4: the telescoping `Λ(z_k) h(z_k) / h(z) = h(z)⁻¹ ∫ g(T + s) q_s(z_k) ds`.
  refine lintegral_congr_ae ?_
  filter_upwards [ae_lastPoint hpos ⟨h0, htop⟩ (k := k)] with zs hzs
  have hΛ : Λ (lastPoint z zs) = (∫⁻ s in Ioi 0, g (T + s) * q s (lastPoint z zs)) *
      (h (lastPoint z zs))⁻¹ := by
    rw [hΛdef, lifetimeFunctional, ← lintegral_mul_const]
    · refine lintegral_congr fun s => ?_
      rw [div_eq_mul_inv, mul_assoc]
    · exact hgT.mul (hq.comp (measurable_id.prodMk measurable_const))
  have hc : (h (lastPoint z zs))⁻¹ * h (lastPoint z zs) = 1 :=
    ENNReal.inv_mul_cancel hzs.1 hzs.2
  rw [hΛ, doobFddDensity, div_eq_mul_inv]
  calc F zs * ((∫⁻ s in Ioi 0, g (T + s) * q s (lastPoint z zs)) * (h (lastPoint z zs))⁻¹) *
        (fddDensity p z ts zs * (h (lastPoint z zs) * (h z)⁻¹))
      = (h z)⁻¹ * (F zs * fddDensity p z ts zs *
          ∫⁻ s in Ioi 0, g (T + s) * q s (lastPoint z zs)) *
          ((h (lastPoint z zs))⁻¹ * h (lastPoint z zs)) := by ring
    _ = _ := by rw [hc, mul_one]

end Killed

end BlockBand.Diffusion
