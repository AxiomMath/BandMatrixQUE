module

public import BlockBand.Endpoints.Poisson.PoissonEndpointRings
public import BlockBand.QUE.Fourier.PhysicalWeightedMass
public import BlockBand.Model.Construction.SpectralFiniteRealization

/-!
# The Poisson Laplace limit from the same-volume comparison

We derive the Poisson Laplace limit from the same-volume log-error bound. Steps 1–4 are those
of the proof of the Poisson endpoint theorem in the paper.

* `pe_laplace_chain`: Step 1. A coupling and `|e^{-a} - e^{-b}| ≤ |a - b|` for `a, b ≥ 0`
  reduce the Laplace comparison to the three moves
  `Tr f → 𝓡_δ^C(H^ring) → 𝓡_δ^C(H^boxes) → Σᵢ Yᵢ`.
* `pe_part`, `pe_sum_part`, `pe_part_real`: nearly equal box lengths.
* `pe_realization_integral`: the physical Laplace functional of a realization through the
  raw spectral sum `rawUnfoldedSpectralSum` (a.s. equal).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.InputsRing
open BlockBand.Model.Construction
open scoped ENNReal

/-- `|e^{-a} - e^{-b}| ≤ |a - b|` for `a, b ≥ 0` (Step 1 of the proof). -/
theorem pe_abs_exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  rcases le_total a b with hab | hab
  · have h1 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-a) - Real.exp (-b) ≤ b - a := by
      have := Real.add_one_le_exp (-(b - a))
      have e : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
        rw [← Real.exp_add]; ring_nf
      have ha1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      nlinarith [Real.exp_pos (-a)]
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h1 : Real.exp (-a) ≤ Real.exp (-b) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-b) - Real.exp (-a) ≤ a - b := by
      have := Real.add_one_le_exp (-(a - b))
      have e : Real.exp (-a) = Real.exp (-b) * Real.exp (-(a - b)) := by
        rw [← Real.exp_add]; ring_nf
      have hb1 : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      nlinarith [Real.exp_pos (-b)]
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- **Step 1 of the proof**: comparison of two Laplace functionals through
the positive statistics. `γ` couples `μ` and `ν`; `A, B ≥ 0`; then
`|E_μ e^{-A} - E_ν e^{-B}| ≤ E_μ|R₁ - A| + E_γ|R₁ - R₂| + E_ν|R₂ - B|`. -/
theorem pe_laplace_chain {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (γ : Measure (α × β)) [IsProbabilityMeasure γ] (hfst : γ.map Prod.fst = μ)
    (hsnd : γ.map Prod.snd = ν) {A R₁ : α → ℝ} {B R₂ : β → ℝ} (hA : Measurable A)
    (hR₁ : Measurable R₁) (hB : Measurable B) (hR₂ : Measurable R₂) (hA0 : ∀ x, 0 ≤ A x)
    (hB0 : ∀ y, 0 ≤ B y) {e₁ e₂ e₃ : ℝ} (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (he₃ : 0 ≤ e₃)
    (h₁ : ∫⁻ x, ENNReal.ofReal |R₁ x - A x| ∂μ ≤ ENNReal.ofReal e₁)
    (h₂ : ∫⁻ z, ENNReal.ofReal |R₁ z.1 - R₂ z.2| ∂γ ≤ ENNReal.ofReal e₂)
    (h₃ : ∫⁻ y, ENNReal.ofReal |R₂ y - B y| ∂ν ≤ ENNReal.ofReal e₃) :
    |(∫ x, Real.exp (-A x) ∂μ) - ∫ y, Real.exp (-B y) ∂ν| ≤ e₁ + e₂ + e₃ := by
  have hmA : Measurable fun x => Real.exp (-A x) := Real.measurable_exp.comp hA.neg
  have hmB : Measurable fun y => Real.exp (-B y) := Real.measurable_exp.comp hB.neg
  have hI1 : (∫ x, Real.exp (-A x) ∂μ) = ∫ z, Real.exp (-A z.1) ∂γ := by
    rw [← hfst, integral_map measurable_fst.aemeasurable hmA.aestronglyMeasurable]
  have hI2 : (∫ y, Real.exp (-B y) ∂ν) = ∫ z, Real.exp (-B z.2) ∂γ := by
    rw [← hsnd, integral_map measurable_snd.aemeasurable hmB.aestronglyMeasurable]
  have hiA : Integrable (fun z : α × β => Real.exp (-A z.1)) γ :=
    (pe_integral_exp_neg γ (hA.comp measurable_fst) (fun z => hA0 z.1)).1
  have hiB : Integrable (fun z : α × β => Real.exp (-B z.2)) γ :=
    (pe_integral_exp_neg γ (hB.comp measurable_snd) (fun z => hB0 z.2)).1
  rw [hI1, hI2, ← integral_sub hiA hiB]
  refine (abs_integral_le_integral_abs).trans ?_
  have hm : Measurable fun z : α × β => |Real.exp (-A z.1) - Real.exp (-B z.2)| :=
    ((hmA.comp measurable_fst).sub (hmB.comp measurable_snd)).abs
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => abs_nonneg _)
    hm.aestronglyMeasurable]
  have hpt : ∀ z : α × β, ENNReal.ofReal |Real.exp (-A z.1) - Real.exp (-B z.2)| ≤
      ENNReal.ofReal |R₁ z.1 - A z.1| + ENNReal.ofReal |R₁ z.1 - R₂ z.2| +
        ENNReal.ofReal |R₂ z.2 - B z.2| := by
    intro z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ((pe_abs_exp_neg_sub_exp_neg_le (hA0 z.1) (hB0 z.2)).trans ?_)
    have e : A z.1 - B z.2 = -(R₁ z.1 - A z.1) + (R₁ z.1 - R₂ z.2) + (R₂ z.2 - B z.2) := by ring
    rw [e, ← abs_neg (R₁ z.1 - A z.1)]
    refine (abs_add_le _ _).trans ?_
    gcongr
    exact abs_add_le _ _
  have hm1 : Measurable fun x => ENNReal.ofReal |R₁ x - A x| :=
    ENNReal.measurable_ofReal.comp (hR₁.sub hA).abs
  have hm3 : Measurable fun y => ENNReal.ofReal |R₂ y - B y| :=
    ENNReal.measurable_ofReal.comp (hR₂.sub hB).abs
  have hm1' : Measurable fun z : α × β => ENNReal.ofReal |R₁ z.1 - A z.1| :=
    hm1.comp measurable_fst
  have hm3' : Measurable fun z : α × β => ENNReal.ofReal |R₂ z.2 - B z.2| :=
    hm3.comp measurable_snd
  have hl1 : ∫⁻ z, ENNReal.ofReal |R₁ z.1 - A z.1| ∂γ = ∫⁻ x, ENNReal.ofReal |R₁ x - A x| ∂μ := by
    rw [← hfst, lintegral_map hm1 measurable_fst]
  have hl3 : ∫⁻ z, ENNReal.ofReal |R₂ z.2 - B z.2| ∂γ = ∫⁻ y, ENNReal.ofReal |R₂ y - B y| ∂ν := by
    rw [← hsnd, lintegral_map hm3 measurable_snd]
  have hle : ∫⁻ z, ENNReal.ofReal |Real.exp (-A z.1) - Real.exp (-B z.2)| ∂γ ≤
      ENNReal.ofReal (e₁ + e₂ + e₃) := by
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_add_right _ hm3', lintegral_add_left hm1', hl1, hl3,
      ENNReal.ofReal_add (by positivity) he₃, ENNReal.ofReal_add he₁ he₂]
    gcongr
  have hfin : ENNReal.ofReal (e₁ + e₂ + e₃) ≠ ∞ := ENNReal.ofReal_ne_top
  calc (∫⁻ z, ENNReal.ofReal |Real.exp (-A z.1) - Real.exp (-B z.2)| ∂γ).toReal
      ≤ (ENNReal.ofReal (e₁ + e₂ + e₃)).toReal := ENNReal.toReal_mono hfin hle
    _ = e₁ + e₂ + e₃ := ENNReal.toReal_ofReal (by positivity)

/-- The physical Laplace functional of a realization through the raw spectral sum. -/
theorem pe_realization_integral {p : Parameters} (R : FiniteRealization p) (E : ℝ)
    (f : ℝ → ℝ) :
    ∫ H, Real.exp (-∑ α, f (R.spectral.unfoldedEigenvalue E H α))
        ∂(R.model.law : Measure p.SiteMatrix) =
      ∫ H, Real.exp (-rawUnfoldedSpectralSum H E ((p.N : ℝ) * Parameters.semicircleDensity E) f)
        ∂(R.model.law : Measure p.SiteMatrix) := by
  refine integral_congr_ae ?_
  filter_upwards [BlockBand.QUE.Fourier.spectral_eigenvalue_eq_canonical_ae R.spectral] with H heig
  congr 2
  unfold rawUnfoldedSpectralSum
  refine (Fintype.sum_equiv (finCongr (physicalSite_card p)) _ _ fun i => ?_).symm
  simp only [Parameters.SpectralRealization.unfoldedEigenvalue, heig, physicalOrderedEigenvalue,
    physicalSpectralRank]
  congr 3

/-- Nearly equal parts of `n` blocks into `m` boxes: `⌊n(i+1)/m⌋ - ⌊ni/m⌋`. -/
def pe_part (n m : ℕ) (i : Fin m) : ℕ := n * (i.1 + 1) / m - n * i.1 / m

theorem pe_sum_part (n m : ℕ) (hm : 0 < m) : ∑ i : Fin m, pe_part n m i = n := by
  have key : ∀ k : ℕ, ∑ i ∈ Finset.range k, (n * (i + 1) / m - n * i / m) = n * k / m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have : n * k / m ≤ n * (k + 1) / m := Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
      omega
  have := key m
  rw [Nat.mul_div_cancel _ hm, ← Fin.sum_univ_eq_sum_range (fun i => n * (i + 1) / m - n * i / m)]
    at this
  exact this

theorem pe_part_ge (n m : ℕ) (i : Fin m) : n / m ≤ pe_part n m i := by
  unfold pe_part
  have h : n * i.1 / m + n / m ≤ (n * i.1 + n) / m := Nat.div_add_div_le_add_div
  rw [show n * i.1 + n = n * (i.1 + 1) by ring] at h
  omega

theorem pe_part_real (n m : ℕ) (hm : 0 < m) (i : Fin m) :
    (n : ℝ) / m - 1 < pe_part n m i ∧ (pe_part n m i : ℝ) < n / m + 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : ∀ x : ℕ, (x : ℝ) / m - 1 < ((x / m : ℕ) : ℝ) ∧ ((x / m : ℕ) : ℝ) ≤ x / m := by
    intro x
    refine ⟨?_, Nat.cast_div_le⟩
    have hx := Nat.div_add_mod x m
    have hmod := Nat.mod_lt x hm
    have : (x : ℝ) = m * ((x / m : ℕ) : ℝ) + ((x % m : ℕ) : ℝ) := by exact_mod_cast hx.symm
    have hmod' : ((x % m : ℕ) : ℝ) < m := by exact_mod_cast hmod
    rw [div_sub_one hmR.ne', div_lt_iff₀ hmR]
    nlinarith
  have hle : n * i.1 / m ≤ n * (i.1 + 1) / m := Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
  unfold pe_part
  rw [Nat.cast_sub hle]
  obtain ⟨a1, a2⟩ := hb (n * (i.1 + 1))
  obtain ⟨b1, b2⟩ := hb (n * i.1)
  push_cast at a1 a2 b1 b2
  constructor
  · have : (n : ℝ) * (i.1 + 1) / m - n * i.1 / m = n / m := by field_simp; ring
    linarith
  · have : (n : ℝ) * (i.1 + 1) / m - n * i.1 / m = n / m := by field_simp; ring
    linarith

/-- `δ(1 + |log δ|) → 0` as `δ ↓ 0`: a small admissible `δ`. -/
theorem pe_exists_delta (A θ : ℝ) (hA : 0 ≤ A) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ A * (δ * (1 + |Real.log δ|)) ≤ θ := by
  have hc : Continuous fun x : ℝ => x + |x * Real.log x| :=
    continuous_id.add (Real.continuous_mul_log.abs)
  have h0 : Tendsto (fun x : ℝ => x + |x * Real.log x|) (𝓝 0) (𝓝 0) := by
    simpa using hc.tendsto 0
  obtain ⟨r, hr, hball⟩ := Metric.tendsto_nhds_nhds.1 h0 (θ / (A + 1)) (by positivity)
  refine ⟨r / 2, half_pos hr, ?_⟩
  have hx := hball (x := r / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]; linarith)
  rw [Real.dist_eq, sub_zero] at hx
  have he : r / 2 * (1 + |Real.log (r / 2)|) = r / 2 + |r / 2 * Real.log (r / 2)| := by
    rw [abs_mul, abs_of_pos (half_pos hr)]; ring
  rw [he]
  have hnn : 0 ≤ r / 2 + |r / 2 * Real.log (r / 2)| := by positivity
  rw [abs_of_nonneg hnn] at hx
  calc A * (r / 2 + |r / 2 * Real.log (r / 2)|) ≤ (A + 1) * (θ / (A + 1)) := by
        apply mul_le_mul (by linarith) hx.le hnn (by linarith)
    _ = θ := by field_simp

open BlockBand.External.PSSS in
/-- **The Poisson Laplace limit** from the same-volume log-error bound `PeSameVolumeLogError`.
Proof: Step 1 (`pe_laplace_chain`) and Step 2 (summing the errors, with
`|B|/n ≤ 2m(1 + 2R)/τ`). For Step 3 the parameters are chosen in the order δ, then `m`, then
`R`, then `τ₀`. This choice gives the limit; the paper's choice `m ≍ √τ`, `R = A log(2+τ)`
also gives a rate. Step 4 (the order of limits) is the quantifier order of
`PoissonEndpointLaplace`. -/
theorem poissonEndpointLaplace_of_sameVolume (source : SourceContract.{0})
    (hDens : CriticalDensityEstimate) (hRing : RingBlockModels) (hWegner : ProjectedWegner)
    (hCount : ConditionalBlockGUECount) (hSV : PeSameVolumeLogError) :
    PoissonEndpointLaplace := by
  intro b hb hb' E hE hE' f hfs hf0 η hη
  set ρE := Parameters.semicircleDensity E with hρE_def
  have hρE : 0 < ρE := lmf_semicircleDensity_pos hE hE'
  obtain ⟨Cf, hCf, hring, hbox⟩ := finiteLogRecovery_ring_and_ringSum hRing hWegner hCount b hb
    hb' ρE hρE f hfs f.hasCompactSupport hf0
  obtain ⟨K, hK, hind⟩ := pe_independentRingLaplace source hDens b hb hb' E hE hE' f f.continuous
    f.hasCompactSupport hf0
  obtain ⟨c, hc, hSVf⟩ := hSV b hb hb' E hE hE' f hfs f.hasCompactSupport hf0
  obtain ⟨δ, hδ, hδb⟩ := pe_exists_delta (2 * Cf) (η / 5) (by positivity) (by positivity)
  obtain ⟨C, hC0, hSVδ⟩ := hSVf δ hδ
  -- the number of boxes
  set m : ℕ := ⌈5 * K / η⌉₊ + 1 with hm_def
  have hm : 0 < m := Nat.succ_pos _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hKm : K / m ≤ η / 5 := by
    rw [div_le_iff₀ hmR]
    have h1 : 5 * K / η ≤ (m : ℝ) := by
      have := Nat.le_ceil (5 * K / η)
      rw [hm_def]; push_cast; linarith
    rw [div_le_iff₀ hη] at h1
    linarith
  -- the buffer length
  obtain ⟨R, hR2, hRb⟩ : ∃ R : ℝ, 2 ≤ R ∧ C * (m : ℝ) ^ 3 * Real.exp (-(c * R)) ≤ η / 5 := by
    have ht : Tendsto (fun R : ℝ => C * (m : ℝ) ^ 3 * Real.exp (-(c * R))) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
      simpa using this.const_mul (C * (m : ℝ) ^ 3)
    obtain ⟨R, h1, h2⟩ := (((tendsto_order.1 ht).2 (η / 5) (by positivity)).and
      (eventually_ge_atTop 2)).exists
    exact ⟨R, h2, h1.le⟩
  refine ⟨max 1 (max ((4 * R + 1) * m) (20 * Cf * m * (1 + 2 * R) / η)), ?_⟩
  intro τ hτ s Rr
  have hτ1 : 1 ≤ τ := le_of_max_le_left hτ
  have hτm : (4 * R + 1) * m ≤ τ := le_trans (le_max_left _ _) (le_of_max_le_right hτ)
  have hτC : 20 * Cf * m * (1 + 2 * R) / η ≤ τ := le_trans (le_max_right _ _) (le_of_max_le_right hτ)
  have hτ0 : 0 < τ := by linarith
  -- the partition
  set a : Fin m → ℝ := fun _ => 1 / m with ha_def
  have hsuma : ∑ i, a i = 1 := by
    simp only [ha_def, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hlen : ∀ i, 4 * R + 1 ≤ a i * τ := fun i => by
    simp only [ha_def]
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hmR]
    exact hτm
  set nb : ℕ → Fin m → ℕ := fun j i => max 4 (pe_part (s.n j) m i) with hnb_def
  have hnb : ∀ j i, 4 ≤ nb j i := fun j i => le_max_left _ _
  have hWr : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  have hnW : ∀ᶠ j in atTop, τ / 2 ≤ (s.n j : ℝ) / s.W j :=
    (tendsto_order.1 s.ratio_tendsto).1 _ (by linarith) |>.mono fun _ h => h.le
  have hnlarge : ∀ᶠ j in atTop, 4 * m ≤ s.n j := by
    have hW' : ∀ᶠ j in atTop, 8 * (m : ℝ) / τ ≤ s.W j :=
      (tendsto_atTop.1 hWr) _
    filter_upwards [hnW, hW'] with j h1 h2
    have hWj : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
    rw [le_div_iff₀ hWj] at h1
    rw [div_le_iff₀ hτ0] at h2
    have : (4 * m : ℝ) ≤ s.n j := by nlinarith
    exact_mod_cast this
  have hnbeq : ∀ᶠ j in atTop, ∀ i, nb j i = pe_part (s.n j) m i := by
    filter_upwards [hnlarge] with j hj i
    have h1 : 4 ≤ s.n j / m := (Nat.le_div_iff_mul_le hm).2 (by linarith)
    exact max_eq_right (h1.trans (pe_part_ge _ _ _))
  have hsumev : ∀ᶠ j in atTop, ∑ i, nb j i = s.n j := by
    filter_upwards [hnbeq] with j hj
    simp_rw [hj]
    exact pe_sum_part _ _ hm
  have hratio : ∀ i, Tendsto (fun j => (nb j i : ℝ) / (s.W j : ℝ)) atTop (𝓝 (a i * τ)) := by
    intro i
    have hlim : Tendsto (fun j => (s.n j : ℝ) / s.W j / m) atTop (𝓝 (a i * τ)) := by
      have e : a i * τ = τ / m := by simp only [ha_def]; ring
      rw [e]
      exact s.ratio_tendsto.div_const (m : ℝ)
    have hinv : Tendsto (fun j => 1 / (s.W j : ℝ)) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.comp hWr
      refine this.congr fun j => ?_
      simp [one_div]
    have hlo := hlim.sub hinv
    have hhi := hlim.add hinv
    rw [sub_zero] at hlo
    rw [add_zero] at hhi
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [hnbeq] with j hj
      have hWj : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
      rw [hj i]
      have := (pe_part_real (s.n j) m hm i).1
      have e : (s.n j : ℝ) / s.W j / m - 1 / s.W j = ((s.n j : ℝ) / m - 1) / s.W j := by
        field_simp
      rw [e]
      exact div_le_div_of_nonneg_right this.le hWj.le
    · filter_upwards [hnbeq] with j hj
      have hWj : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
      rw [hj i]
      have := (pe_part_real (s.n j) m hm i).2
      have e : (s.n j : ℝ) / s.W j / m + 1 / s.W j = ((s.n j : ℝ) / m + 1) / s.W j := by
        field_simp
      rw [e]
      exact div_le_div_of_nonneg_right this.le hWj.le
  set boxes : ∀ j i, (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb').GaussianRingModel :=
    fun j i => (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb').constructGaussianRingModel
  have hSVj := hSVδ m a R τ hR2 hτ1 hsuma hlen s (fun j => (Rr j).model) nb hnb hratio hsumev
    boxes (η / 20) (by positivity)
  have hindj := hind m a τ hτ0 (fun i => by simp only [ha_def]; positivity) hsuma s.W s.W_pos
    s.width_tendsto nb hnb hratio boxes (η / 20) (by positivity)
  have hW3 : ∀ᶠ j in atTop, (3 : ℝ) ≤ s.W j := (tendsto_atTop.1 hWr) 3
  filter_upwards [hSVj, hindj, hsumev, hnW, hW3] with j hSVj hindj hsumj hnWj hW3j
  obtain ⟨Cr, Cb, hCr, hCb, γ, hγ, hfst, hsnd, hlint⟩ := hSVj
  have hsumpos : 0 < ∑ i, nb j i := by rw [hsumj]; have := s.n_ge_four j; omega
  obtain ⟨hri, hrle⟩ := hring (s.parameters b hb hb' j) rfl (Rr j).model E δ hδ Cr
  obtain ⟨hbi, hble⟩ := hbox m (s.W j) (nb j) (hnb j) (s.W_pos j) (boxes j) hsumpos E δ hδ Cb
  -- the omitted fraction `|B|/n ≤ 2m(1 + 2R)/τ`
  have hWj : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
  have hnge : τ * s.W j / 2 ≤ s.n j := by
    rw [le_div_iff₀ hWj] at hnWj; linarith
  have hnpos : (0 : ℝ) < s.n j := lt_of_lt_of_le (by positivity) hnge
  have hfrac : ∀ k : ℝ, k ≤ m * (3 + 2 * R * s.W j) → k / s.n j ≤ 2 * m * (1 + 2 * R) / τ := by
    intro k hk
    have hk' : k ≤ m * (1 + 2 * R) * s.W j := by nlinarith
    rw [div_le_div_iff₀ hnpos hτ0]
    nlinarith [mul_le_mul_of_nonneg_right hk' hτ0.le,
      mul_le_mul_of_nonneg_left hnge (show (0 : ℝ) ≤ 2 * m * (1 + 2 * R) by positivity)]
  have hr := hfrac _ hCr
  have hbfr : (((Cbᶜ).card : ℕ) : ℝ) / ((∑ i, nb j i : ℕ) : ℝ) ≤ 2 * m * (1 + 2 * R) / τ := by
    have : ((∑ i, nb j i : ℕ) : ℝ) = s.n j := by exact_mod_cast hsumj
    rw [this]; exact hfrac _ hCb
  -- the integrands
  have hφ : Measurable (fun X : ∀ i, (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb
      hb').SiteMatrix => directSumBlockCoords (nb j) (fun i => toBlockCoords
        (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb') (X i))) := by
    have h0 : Measurable (fun X : ∀ i, (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j)
        hb hb').SiteMatrix => fun i => toBlockCoords
          (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb') (X i)) :=
      Measurable.of_eval fun i => (measurable_toBlockCoords _).comp (measurable_pi_apply i)
    exact (measurable_directSumBlockCoords (W := s.W j) (nb j)).comp h0
  have hfm : Measurable (f : ℝ → ℝ) := f.continuous.measurable
  have : IsProbabilityMeasure γ := hγ
  have h1 : ∫⁻ H, ENNReal.ofReal |positiveLogStatistic H E
        (((s.parameters b hb hb' j).N : ℝ) * ρE) δ
        (physicalBlockProjector (s.parameters b hb hb' j) Cr) f -
      rawUnfoldedSpectralSum H E (((s.parameters b hb hb' j).N : ℝ) * ρE) f|
      ∂((Rr j).model.law : Measure (s.parameters b hb hb' j).SiteMatrix) ≤
      ENNReal.ofReal (Cf * (δ * (1 + |Real.log δ|) +
        (((Crᶜ).card : ℕ) : ℝ) / ((s.parameters b hb hb' j).n : ℝ))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hri (Eventually.of_forall fun H => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hrle
  have h3 : ∫⁻ X, ENNReal.ofReal |positiveLogStatistic (directSumBlockCoords (nb j)
          (fun i => toBlockCoords (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb')
            (X i))) E ((((∑ i, nb j i) * s.W j : ℕ) : ℝ) * ρE) δ (blockProjector Cb) f -
        rawUnfoldedSpectralSum (directSumBlockCoords (nb j)
          (fun i => toBlockCoords (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb')
            (X i))) E ((((∑ i, nb j i) * s.W j : ℕ) : ℝ) * ρE) f|
      ∂(Measure.pi fun i => ((boxes j i).law :
        Measure (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb').SiteMatrix)) ≤
      ENNReal.ofReal (Cf * (δ * (1 + |Real.log δ|) +
        (((Cbᶜ).card : ℕ) : ℝ) / ((∑ i, nb j i : ℕ) : ℝ))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hbi (Eventually.of_forall fun H => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hble
  have hchain := pe_laplace_chain ((Rr j).model.law : Measure (s.parameters b hb hb' j).SiteMatrix)
    (Measure.pi fun i => ((boxes j i).law :
      Measure (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb').SiteMatrix)) γ
    hfst hsnd
    (A := fun H => rawUnfoldedSpectralSum H E (((s.parameters b hb hb' j).N : ℝ) * ρE) f)
    (R₁ := fun H => positiveLogStatistic H E (((s.parameters b hb hb' j).N : ℝ) * ρE) δ
        (physicalBlockProjector (s.parameters b hb hb' j) Cr) f)
    (B := fun X => rawUnfoldedSpectralSum (directSumBlockCoords (nb j)
          (fun i => toBlockCoords (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb')
            (X i))) E ((((∑ i, nb j i) * s.W j : ℕ) : ℝ) * ρE) f)
    (R₂ := fun X => positiveLogStatistic (directSumBlockCoords (nb j)
          (fun i => toBlockCoords (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb')
            (X i))) E ((((∑ i, nb j i) * s.W j : ℕ) : ℝ) * ρE) δ (blockProjector Cb) f)
    (measurable_rawUnfoldedSpectralSum E _ hfm)
    (measurable_positiveLogStatistic measurable_id E _ δ _ f.continuous)
    ((measurable_rawUnfoldedSpectralSum E _ hfm).comp hφ)
    (measurable_positiveLogStatistic hφ E _ δ (blockProjector Cb) f.continuous)
    (fun H => Finset.sum_nonneg fun i _ => hf0 _) (fun X => Finset.sum_nonneg fun i _ => hf0 _)
    (mul_nonneg hCf (add_nonneg (mul_nonneg hδ.le (by positivity))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
    (by positivity)
    (mul_nonneg hCf (add_nonneg (mul_nonneg hδ.le (by positivity))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))) h1 hlint h3
  rw [pe_realization_integral (Rr j) E f]
  have hsq : ∑ i, a i ^ 2 = 1 / m := by
    rw [Finset.sum_congr rfl (fun i _ => show a i ^ 2 = (1 / (m : ℝ)) ^ 2 from rfl),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsq] at hindj
  have hτC' : 4 * Cf * m * (1 + 2 * R) / τ ≤ η / 5 := by
    rw [div_le_iff₀ hτ0]
    rw [div_le_iff₀ hη] at hτC
    linarith
  have e1 : Cf * (δ * (1 + |Real.log δ|) + (((Crᶜ).card : ℕ) : ℝ) /
      ((s.parameters b hb hb' j).n : ℝ)) ≤
      Cf * (δ * (1 + |Real.log δ|)) + Cf * (2 * m * (1 + 2 * R) / τ) := by
    rw [mul_add]; exact add_le_add_right (mul_le_mul_of_nonneg_left hr hCf) _
  have e3 : Cf * (δ * (1 + |Real.log δ|) + (((Cbᶜ).card : ℕ) : ℝ) / ((∑ i, nb j i : ℕ) : ℝ)) ≤
      Cf * (δ * (1 + |Real.log δ|)) + Cf * (2 * m * (1 + 2 * R) / τ) := by
    rw [mul_add]; exact add_le_add_right (mul_le_mul_of_nonneg_left hbfr hCf) _
  have hKm' : K * (1 / m) ≤ η / 5 := by rw [mul_one_div]; exact hKm
  have h4 : Cf * (2 * m * (1 + 2 * R) / τ) + Cf * (2 * m * (1 + 2 * R) / τ) =
      4 * Cf * m * (1 + 2 * R) / τ := by ring
  refine (abs_sub_le _ (∫ X, Real.exp (-rawUnfoldedSpectralSum (directSumBlockCoords (nb j)
      (fun i => toBlockCoords (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb')
        (X i))) E ((((∑ i, nb j i) * s.W j : ℕ) : ℝ) * ρE) f)
      ∂(Measure.pi fun i => ((boxes j i).law :
        Measure (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb').SiteMatrix))) _).trans ?_
  linarith

end BlockBand.Endpoints
