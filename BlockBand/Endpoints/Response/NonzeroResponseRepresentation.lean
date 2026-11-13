module

public import BlockBand.Endpoints.Response.NonzeroResponsePath
public import BlockBand.Endpoints.Response.BridgeOccupationDefs

/-!
# The lifetime-bridge representation of the signed response

The mixture step of the nonzero-response proposition: the lifetime bridge lemma mixes these
conditional expectations against a strictly positive lifetime density; their mixture is exactly
`J_{τ,m}`, since the transformed process stays zero after its lifetime. Absolute integrability is
paid by `E∫_0^τ R_s ds < ∞`.

For a continuous test `q` with `|q| ≤ 1`, split `q = q⁺ - q⁻` (`nzr_pos`, `nzr_neg`) and set
`K_r = ∫_{(0,τ]} ρ(t) ∫_{(0,τ]} r(s) 1{s < t} E^{br}_{z,t}[X_s + Y_s] ds dt`
(`nzr_kernelPart`, `ρ = cornerLifetimeDensity`). `nzr_response_eq`: for every realization of the
one-pair boundary dual from `z = (x, y)` that satisfies the finite-dimensional disintegration of
`LifetimeBridgeStatement` at `k = 1`, and a jointly measurable kernel `p`,
`E[1{σ₀ ≤ τ} ∫_0^τ q R] = K_{q⁺} - K_{q⁻}`, with `K_{q^±} ≤ τ(x + y)` (`firstMoment`).

Proof: Carathéodory modification of `R` (a.s. continuous paths, `nzr_caratheodory`), Tonelli in
`(ω, s)`, the `k = 1` disintegration at each `s ∈ (0, τ]`, Tonelli in `(s, t)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-!
### Kernel-side objects
-/

/-- Positive part `q⁺ = max(q, 0)`. -/
def nzr_pos (q : ℝ → ℝ) (s : ℝ) : ℝ := max (q s) 0

/-- Negative part `q⁻ = max(-q, 0)`. -/
def nzr_neg (q : ℝ → ℝ) (s : ℝ) : ℝ := max (-q s) 0

theorem nzr_pos_sub_neg (q : ℝ → ℝ) (s : ℝ) : nzr_pos q s - nzr_neg q s = q s := by
  unfold nzr_pos nzr_neg
  rcases le_total 0 (q s) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- The lifetime indicator `1{t ≤ τ}` as an `ℝ≥0∞`-valued function. -/
def nzr_cut (τ : ℝ) (t : ℝ) : ℝ≥0∞ := (Iic τ).indicator (fun _ => (1 : ℝ≥0∞)) t

theorem nzr_cut_measurable (τ : ℝ) : Measurable (nzr_cut τ) :=
  measurable_const.indicator measurableSet_Iic

open scoped Classical in
/-- `A_r(t) = ∫_{(0,τ]} r(s) 1{s < t} E^{br}_{z,t}[X_s + Y_s] ds`. -/
def nzr_inner (τ : ℝ) (p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) (z : ℝ × ℝ) (r : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc 0 τ, ENNReal.ofReal (r s) * (if s < t then bridgeMeanTotal p z t s else 0)

/-- `K_r = ∫_{(0,∞)} 1{t ≤ τ} ρ(t) A_r(t) dt`. -/
def nzr_kernelPart (D0 τ : ℝ) (p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) (z : ℝ × ℝ) (r : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi 0, nzr_cut τ t * ENNReal.ofReal (cornerLifetimeDensity D0 p z t) *
    nzr_inner τ p z r t

theorem nzr_bfd_one {α : Type*} (p : ℝ → α → α → ℝ) (z e : α) (t s : ℝ) (zs : Fin 1 → α) :
    bridgeFddDensity p z e t ![s] zs = ENNReal.ofReal (p s z (zs 0)) *
      ENNReal.ofReal (p (t - s) (zs 0) e) / ENNReal.ofReal (p t z e) := by
  simp [bridgeFddDensity]

section Kernel

variable {p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ}
  (hpm : Measurable (fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => p w.1 w.2.1 w.2.2))
include hpm

theorem nzr_bridgeMeanTotal_measurable (z : ℝ × ℝ) :
    Measurable (fun w : ℝ × ℝ => bridgeMeanTotal p z w.1 w.2) := by
  unfold bridgeMeanTotal
  simp_rw [nzr_bfd_one]
  have h1 : Measurable fun v : (ℝ × ℝ) × (Fin 1 → ℝ × ℝ) => p v.1.2 z (v.2 0) :=
    hpm.comp (f := fun v : (ℝ × ℝ) × (Fin 1 → ℝ × ℝ) => (v.1.2, z, v.2 0)) (by fun_prop)
  have h2 : Measurable fun v : (ℝ × ℝ) × (Fin 1 → ℝ × ℝ) => p (v.1.1 - v.1.2) (v.2 0) (0, 0) :=
    hpm.comp (f := fun v : (ℝ × ℝ) × (Fin 1 → ℝ × ℝ) => (v.1.1 - v.1.2, v.2 0, ((0 : ℝ), (0 : ℝ))))
      (by fun_prop)
  have h3 : Measurable fun v : (ℝ × ℝ) × (Fin 1 → ℝ × ℝ) => p v.1.1 z (0, 0) :=
    hpm.comp (f := fun v : (ℝ × ℝ) × (Fin 1 → ℝ × ℝ) => (v.1.1, z, ((0 : ℝ), (0 : ℝ))))
      (by fun_prop)
  have h4 : Measurable fun v : (ℝ × ℝ) × (Fin 1 → ℝ × ℝ) => (v.2 0).1 + (v.2 0).2 := by
    fun_prop
  have : Measurable fun v : (ℝ × ℝ) × (Fin 1 → ℝ × ℝ) =>
      ENNReal.ofReal ((v.2 0).1 + (v.2 0).2) *
        (ENNReal.ofReal (p v.1.2 z (v.2 0)) * ENNReal.ofReal (p (v.1.1 - v.1.2) (v.2 0) (0, 0)) /
          ENNReal.ofReal (p v.1.1 z (0, 0))) :=
    (ENNReal.measurable_ofReal.comp h4).mul
      (((ENNReal.measurable_ofReal.comp h1).mul (ENNReal.measurable_ofReal.comp h2)).div
        (ENNReal.measurable_ofReal.comp h3))
  exact this.lintegral_prod_right'

theorem nzr_rho_measurable (D0 : ℝ) (z : ℝ × ℝ) :
    Measurable fun t => ENNReal.ofReal (cornerLifetimeDensity D0 p z t) := by
  unfold cornerLifetimeDensity
  have : Measurable fun t : ℝ => p t z (0, 0) :=
    hpm.comp (f := fun t : ℝ => (t, z, ((0 : ℝ), (0 : ℝ)))) (by fun_prop)
  exact ENNReal.measurable_ofReal.comp (measurable_const.mul this)

open scoped Classical in
/-- Joint measurability of `(t, s) ↦ 1{t ≤ τ} ρ(t) 1{s < t} E^{br}_{z,t}[X_s+Y_s]`. -/
theorem nzr_mixand_measurable (D0 τ : ℝ) (z : ℝ × ℝ) :
    Measurable fun w : ℝ × ℝ => nzr_cut τ w.1 *
      ENNReal.ofReal (cornerLifetimeDensity D0 p z w.1) *
        (if w.2 < w.1 then bridgeMeanTotal p z w.1 w.2 else 0) := by
  refine (((nzr_cut_measurable τ).comp measurable_fst).mul
    ((nzr_rho_measurable hpm D0 z).comp measurable_fst)).mul ?_
  exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
    (nzr_bridgeMeanTotal_measurable hpm z) measurable_const

theorem nzr_inner_measurable (τ : ℝ) (z : ℝ × ℝ) {r : ℝ → ℝ} (hr : Measurable r) :
    Measurable (nzr_inner τ p z r) := by
  classical
  unfold nzr_inner
  have : Measurable fun w : ℝ × ℝ => ENNReal.ofReal (r w.2) *
      (if w.2 < w.1 then bridgeMeanTotal p z w.1 w.2 else 0) :=
    (ENNReal.measurable_ofReal.comp (hr.comp measurable_snd)).mul
      (Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
        (nzr_bridgeMeanTotal_measurable hpm z) measurable_const)
  convert this.lintegral_prod_right' (ν := volume.restrict (Ioc 0 τ)) using 3

theorem nzr_bmt_measurable_right (z : ℝ × ℝ) (t : ℝ) :
    Measurable fun s => bridgeMeanTotal p z t s :=
  Measurable.of_uncurry_left (f := fun t s => bridgeMeanTotal p z t s)
    (nzr_bridgeMeanTotal_measurable hpm z)

open scoped Classical in
theorem nzr_mixand_measurable_left (D0 τ : ℝ) (z : ℝ × ℝ) (s : ℝ) :
    Measurable fun t => nzr_cut τ t * ENNReal.ofReal (cornerLifetimeDensity D0 p z t) *
        (if s < t then bridgeMeanTotal p z t s else 0) :=
  Measurable.of_uncurry_right (f := fun t s => nzr_cut τ t *
      ENNReal.ofReal (cornerLifetimeDensity D0 p z t) *
        (if s < t then bridgeMeanTotal p z t s else 0))
    (nzr_mixand_measurable hpm D0 τ z)

open scoped Classical in
theorem nzr_swapped_measurable (D0 τ : ℝ) (z : ℝ × ℝ) {r : ℝ → ℝ} (hr : Measurable r) :
    Measurable fun w : ℝ × ℝ => ENNReal.ofReal (r w.1) * (nzr_cut τ w.2 *
      ENNReal.ofReal (cornerLifetimeDensity D0 p z w.2) *
        (if w.1 < w.2 then bridgeMeanTotal p z w.2 w.1 else 0)) := by
  have hM : Measurable fun w : ℝ × ℝ => bridgeMeanTotal p z w.2 w.1 :=
    (nzr_bridgeMeanTotal_measurable hpm z).comp (f := Prod.swap) measurable_swap
  exact (ENNReal.measurable_ofReal.comp (hr.comp measurable_fst)).mul
    ((((nzr_cut_measurable τ).comp measurable_snd).mul
      ((nzr_rho_measurable hpm D0 z).comp measurable_snd)).mul
        (Measurable.ite (measurableSet_lt measurable_fst measurable_snd) hM measurable_const))

theorem nzr_inner_integrand_measurable (z : ℝ × ℝ) {r : ℝ → ℝ} (hr : Measurable r) (t : ℝ) :
    Measurable fun s => ENNReal.ofReal (r s) *
      (if s < t then bridgeMeanTotal p z t s else 0) := by
  classical
  exact (ENNReal.measurable_ofReal.comp hr).mul
    (Measurable.ite (measurableSet_lt measurable_id measurable_const)
      (nzr_bmt_measurable_right hpm z t) measurable_const)

end Kernel

/-!
### The representation for one realization
-/

open scoped Classical in
/-- The `k = 1` disintegration of `LifetimeBridgeStatement` for one realization. -/
def nzr_FddOne (D0 : ℝ) (p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) (x y : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) : Prop :=
  ∀ (k : ℕ) (ts : Fin k → ℝ), StrictMono ts → (∀ i, 0 < ts i) →
    ∀ g : ℝ → ℝ≥0∞, Measurable g → ∀ F : (Fin k → ℝ × ℝ) → ℝ≥0∞, Measurable F →
      ∫⁻ ω, (if dualExtinction N ω < ⊤ ∧ ∀ i, ENNReal.ofReal (ts i) < dualExtinction N ω
          then g (dualExtinction N ω).toReal * F (fun i => dualPoint X Y (ts i) ω)
          else 0) ∂P =
        ∫⁻ t in Ioi 0, g t * ENNReal.ofReal (cornerLifetimeDensity D0 p (x, y) t) *
          (if ∀ i, ts i < t then ∫⁻ zs, F zs * bridgeFddDensity p (x, y) (0, 0) t ts zs else 0)

section Realization

variable {D0 τ x y : ℝ} {p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ}
  {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m} {P : Measure Ω}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- One time `s > 0` of the disintegration: `E[1{σ₀ ≤ τ} R_s] = ∫ 1{t ≤ τ} ρ(t) 1{s<t} m_t(s) dt`,
for any process `R'` equal a.s. (for all times) to `R`. -/
theorem nzr_one_time (hR : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    (hfdd : nzr_FddOne D0 p x y P N X Y) {R' : ℝ → Ω → ℝ}
    (hR'ae : ∀ᵐ ω ∂P, ∀ s, R' s ω =
      dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω))
    (τ : ℝ) (hτ : 0 ≤ τ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ ω, (if N τ.toNNReal ω = 0 then ENNReal.ofReal (R' s ω) else 0) ∂P =
      ∫⁻ t in Ioi 0, nzr_cut τ t * ENNReal.ofReal (cornerLifetimeDensity D0 p (x, y) t) *
        (if s < t then bridgeMeanTotal p (x, y) t s else 0) := by
  classical
  have hF : Measurable fun zs : Fin 1 → ℝ × ℝ => ENNReal.ofReal ((zs 0).1 + (zs 0).2) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have h := hfdd 1 ![s] (fun i j hij => absurd hij (by fin_cases i; fin_cases j; simp))
    (fun i => by fin_cases i; simpa using hs) (nzr_cut τ) (nzr_cut_measurable τ) _ hF
  have hrhs : ∀ t, (if ∀ i : Fin 1, (![s] : Fin 1 → ℝ) i < t then
        ∫⁻ zs, ENNReal.ofReal ((zs 0).1 + (zs 0).2) * bridgeFddDensity p (x, y) (0, 0) t ![s] zs
        else 0) = if s < t then bridgeMeanTotal p (x, y) t s else 0 := by
    intro t
    simp only [Fin.forall_fin_one, Matrix.cons_val_zero, bridgeMeanTotal]
  simp_rw [hrhs] at h
  rw [← h]
  refine lintegral_congr_ae ?_
  filter_upwards [isBoundaryDualProcess_ae_path hR, hR'ae] with ω hω hω'
  obtain ⟨hp, h0, -, -⟩ := hω
  rw [hω' s]
  simp only [Fin.forall_fin_one, Matrix.cons_val_zero, dualPoint]
  have hτiff : N τ.toNNReal ω = 0 ↔ dualExtinction N ω ≤ ENNReal.ofReal τ :=
    nzr_level_zero_iff hp τ.toNNReal
  by_cases hsz : ENNReal.ofReal s < dualExtinction N ω
  · have h1 : N s.toNNReal ω = 1 := (nzr_level_one_iff hp h0 s.toNNReal).2 hsz
    rw [h1, dualTotal_one]
    by_cases hfin : dualExtinction N ω < ⊤
    · rw [ite_eq_left (show dualExtinction N ω < ⊤ ∧ ENNReal.ofReal s < dualExtinction N ω from
        ⟨hfin, hsz⟩)]
      have hcut : nzr_cut τ (dualExtinction N ω).toReal =
          if N τ.toNNReal ω = 0 then 1 else 0 := by
        unfold nzr_cut
        by_cases hz : N τ.toNNReal ω = 0
        · rw [ite_eq_left hz, indicator_of_mem]
          have := hτiff.1 hz
          exact (ENNReal.le_ofReal_iff_toReal_le hfin.ne hτ).1 this
        · rw [ite_eq_right hz, indicator_of_notMem]
          intro hmem
          exact hz (hτiff.2 ((ENNReal.le_ofReal_iff_toReal_le hfin.ne hτ).2 hmem))
      rw [hcut]
      split_ifs <;> simp
    · rw [ite_eq_right (show ¬(dualExtinction N ω < ⊤ ∧ ENNReal.ofReal s < dualExtinction N ω) from
        fun h => hfin h.1)]
      have : ¬ N τ.toNNReal ω = 0 := fun hz => hfin (lt_of_le_of_lt (hτiff.1 hz)
        ENNReal.ofReal_lt_top)
      rw [ite_eq_right this]
  · rw [ite_eq_right (show ¬(dualExtinction N ω < ⊤ ∧ ENNReal.ofReal s < dualExtinction N ω) from
      fun h => hsz h.2)]
    have h0' : N s.toNNReal ω = 0 := (nzr_level_zero_iff hp s.toNNReal).2 (not_lt.1 hsz)
    rw [h0', dualTotal_zero]
    simp

open scoped Classical in
/-- `a_r(ω) = ∫_{(0,τ]} r(s) 1{N_τ = 0} R'_s ds` (`1{N_τ = 0} = 1{σ₀ ≤ τ}` on good paths). -/
def nzr_omegaPart {Ω : Type*} (τ : ℝ) (N : ℝ≥0 → Ω → ℕ) (R' : ℝ → Ω → ℝ) (r : ℝ → ℝ)
    (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Ioc 0 τ, ENNReal.ofReal (r s) *
    (if N τ.toNNReal ω = 0 then ENNReal.ofReal (R' s ω) else 0)

theorem nzr_pos_continuous {q : ℝ → ℝ} (hq : Continuous q) : Continuous (nzr_pos q) :=
  hq.max continuous_const

theorem nzr_neg_continuous {q : ℝ → ℝ} (hq : Continuous q) : Continuous (nzr_neg q) :=
  hq.neg.max continuous_const

theorem nzr_pos_bounds {q : ℝ → ℝ} (hq1 : ∀ s, |q s| ≤ 1) (s : ℝ) :
    0 ≤ nzr_pos q s ∧ nzr_pos q s ≤ 1 :=
  ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hq1 s)) zero_le_one⟩

theorem nzr_neg_bounds {q : ℝ → ℝ} (hq1 : ∀ s, |q s| ≤ 1) (s : ℝ) :
    0 ≤ nzr_neg q s ∧ nzr_neg q s ≤ 1 :=
  ⟨le_max_right _ _, max_le ((neg_le_abs _).trans (hq1 s)) zero_le_one⟩

/-- **The lifetime-bridge representation of the signed response** for one realization. -/
theorem nzr_response_eq (hτ : 0 < τ) {q : ℝ → ℝ} (hq : Continuous q) (hq1 : ∀ s, |q s| ≤ 1)
    (hpm : Measurable (fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => p w.1 w.2.1 w.2.2))
    (hBdry : DualBoundaryStartContract) (hD0 : 0 < D0) (hds : IsDualStart ![x] ![y])
    (hR : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (hfdd : nzr_FddOne D0 p x y P N X Y) :
    nzr_kernelPart D0 τ p (x, y) (nzr_pos q) ≤ ENNReal.ofReal (τ * (x + y)) ∧
    nzr_kernelPart D0 τ p (x, y) (nzr_neg q) ≤ ENNReal.ofReal (τ * (x + y)) ∧
    ∫ ω, responseIntegrand τ q N X Y ω ∂P =
      (nzr_kernelPart D0 τ p (x, y) (nzr_pos q)).toReal -
        (nzr_kernelPart D0 τ p (x, y) (nzr_neg q)).toReal := by
  classical
  have := hR.prob
  have hgood := isBoundaryDualProcess_ae_path hR
  obtain ⟨R', hR'm, hR's, hR'ae⟩ := nzr_caratheodory (P := P)
    (fun s ω => dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω))
    (nzr_total_measurable hR) (hgood.mono fun ω h => nzr_total_continuous h.1 h.2.1)
  have hNτ : MeasurableSet {ω | N τ.toNNReal ω = 0} :=
    ((hR.adapted τ.toNNReal).1.mono (𝓖.le _) le_rfl) (measurableSet_singleton 0)
  have hint : ∀ r : ℝ → ℝ, Measurable r → Measurable fun w : Ω × ℝ => ENNReal.ofReal (r w.2) *
      (if N τ.toNNReal w.1 = 0 then ENNReal.ofReal (R' w.2 w.1) else 0) := by
    intro r hr
    exact (ENNReal.measurable_ofReal.comp (hr.comp measurable_snd)).mul
      (Measurable.ite (measurable_fst hNτ)
        (ENNReal.measurable_ofReal.comp (hR'm.comp measurable_swap)) measurable_const)
  have ha_meas : ∀ r, Measurable r → Measurable (nzr_omegaPart τ N R' r) := fun r hr =>
    (hint r hr).lintegral_prod_right'
  -- Tonelli and the `k = 1` disintegration
  have ha_eq : ∀ r : ℝ → ℝ, Measurable r →
      ∫⁻ ω, nzr_omegaPart τ N R' r ω ∂P = nzr_kernelPart D0 τ p (x, y) r := by
    intro r hr
    unfold nzr_omegaPart
    rw [lintegral_lintegral_swap (hint r hr).aemeasurable]
    have hstep : ∀ s ∈ Ioc 0 τ, ∫⁻ ω, ENNReal.ofReal (r s) *
        (if N τ.toNNReal ω = 0 then ENNReal.ofReal (R' s ω) else 0) ∂P =
        ∫⁻ t in Ioi 0, ENNReal.ofReal (r s) * (nzr_cut τ t *
          ENNReal.ofReal (cornerLifetimeDensity D0 p (x, y) t) *
            (if s < t then bridgeMeanTotal p (x, y) t s else 0)) := by
      intro s hs
      rw [lintegral_const_mul _ ?_, nzr_one_time hR hfdd hR'ae τ hτ.le hs.1,
        lintegral_const_mul _ ?_]
      · exact nzr_mixand_measurable_left hpm D0 τ (x, y) s
      · exact Measurable.ite hNτ (ENNReal.measurable_ofReal.comp (hR's s)) measurable_const
    rw [setLIntegral_congr_fun measurableSet_Ioc hstep, lintegral_lintegral_swap]
    · unfold nzr_kernelPart nzr_inner
      refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [← lintegral_const_mul]
      · exact lintegral_congr fun s => by ring
      · exact nzr_inner_integrand_measurable hpm (x, y) hr t
    · exact (nzr_swapped_measurable hpm D0 τ (x, y) hr).aemeasurable
  -- the first-moment bound
  have hbound : ∀ r : ℝ → ℝ, (∀ s, 0 ≤ r s ∧ r s ≤ 1) →
      ∫⁻ ω, nzr_omegaPart τ N R' r ω ∂P ≤ ENNReal.ofReal (τ * (x + y)) := by
    intro r hr
    refine le_trans (lintegral_mono_ae ?_)
      (hBdry.firstMoment D0 hD0 x y hds Ω _ 𝓖 P N X Y hR τ hτ.le)
    filter_upwards [hR'ae] with ω hω
    unfold nzr_omegaPart
    refine le_trans (lintegral_mono fun s => ?_) (lintegral_mono_set Ioc_subset_Icc_self)
    rw [hω s]
    calc ENNReal.ofReal (r s) * (if N τ.toNNReal ω = 0 then ENNReal.ofReal
          (dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω)) else 0)
        ≤ 1 * ENNReal.ofReal (dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω)) :=
          mul_le_mul' (ENNReal.ofReal_le_one.2 (hr s).2) (by split_ifs <;> simp)
      _ = _ := one_mul _
  -- the pathwise identity
  have hx0 : 0 ≤ x := by simpa using hds.2.2.1 0
  have hy0 : 0 ≤ y := by simpa using (hds.2.2.2.1 0).1
  have hpath : ∀ᵐ ω ∂P, responseIntegrand τ q N X Y ω =
      (nzr_omegaPart τ N R' (nzr_pos q) ω).toReal -
        (nzr_omegaPart τ N R' (nzr_neg q) ω).toReal := by
    filter_upwards [hgood, hR'ae] with ω hω hω'
    obtain ⟨hp, h0, hX0, hY0⟩ := hω
    have hc : Continuous fun s : ℝ =>
        dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω) :=
      nzr_total_continuous hp h0
    have hnn : ∀ s : ℝ, 0 ≤ dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω) :=
      fun s => boundaryPath_total_nonneg (n := fun t => N t ω) hp h0 (by rw [hX0]; exact hx0)
        (by rw [hY0]; exact hy0) s.toNNReal
    unfold responseIntegrand nzr_omegaPart
    by_cases hz : N τ.toNNReal ω = 0
    · have hζ : dualExtinction N ω ≤ ENNReal.ofReal τ := (nzr_level_zero_iff hp τ.toNNReal).1 hz
      rw [ite_eq_left hζ]
      simp only [hz, ite_true]
      have key : ∀ r : ℝ → ℝ, Continuous r → (∀ s, 0 ≤ r s) →
          ∫ s in Ioc 0 τ, r s * dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω) =
            (∫⁻ s in Ioc 0 τ, ENNReal.ofReal (r s) * ENNReal.ofReal (R' s ω)).toReal := by
        intro r hr hr0
        rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun s => mul_nonneg (hr0 s) (hnn s))
          (hr.mul hc).aestronglyMeasurable]
        congr 1
        refine lintegral_congr fun s => ?_
        rw [hω' s, ENNReal.ofReal_mul (hr0 s)]
      have hip : IntegrableOn (fun s => nzr_pos q s *
          dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω)) (Ioc 0 τ) :=
        ((nzr_pos_continuous hq).mul hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
      have him : IntegrableOn (fun s => nzr_neg q s *
          dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω)) (Ioc 0 τ) :=
        ((nzr_neg_continuous hq).mul hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
      rw [intervalIntegral.integral_of_le hτ.le,
        ← key _ (nzr_pos_continuous hq) fun s => (nzr_pos_bounds hq1 s).1,
        ← key _ (nzr_neg_continuous hq) fun s => (nzr_neg_bounds hq1 s).1, ← integral_sub hip him]
      refine integral_congr_ae (ae_of_all _ fun s => ?_)
      simp only
      rw [← nzr_pos_sub_neg q s]
      ring
    · have hζ : ¬dualExtinction N ω ≤ ENNReal.ofReal τ := fun h =>
        hz ((nzr_level_zero_iff hp τ.toNNReal).2 h)
      rw [ite_eq_right hζ]
      simp [hz]
  have hqpm : Measurable (nzr_pos q) := (nzr_pos_continuous hq).measurable
  have hqmm : Measurable (nzr_neg q) := (nzr_neg_continuous hq).measurable
  have hbp := hbound _ (nzr_pos_bounds hq1)
  have hbm := hbound _ (nzr_neg_bounds hq1)
  have hfp : ∫⁻ ω, nzr_omegaPart τ N R' (nzr_pos q) ω ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbp
  have hfm : ∫⁻ ω, nzr_omegaPart τ N R' (nzr_neg q) ω ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbm
  refine ⟨ha_eq _ hqpm ▸ hbp, ha_eq _ hqmm ▸ hbm, ?_⟩
  rw [integral_congr_ae hpath,
    integral_sub (integrable_toReal_of_lintegral_ne_top (ha_meas _ hqpm).aemeasurable hfp)
      (integrable_toReal_of_lintegral_ne_top (ha_meas _ hqmm).aemeasurable hfm),
    integral_toReal (ha_meas _ hqpm).aemeasurable (ae_lt_top (ha_meas _ hqpm) hfp),
    integral_toReal (ha_meas _ hqmm).aemeasurable (ae_lt_top (ha_meas _ hqmm) hfm),
    ha_eq _ hqpm, ha_eq _ hqmm]

end Realization

end BlockBand.Endpoints
