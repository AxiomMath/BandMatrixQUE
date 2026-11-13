module

public import BlockBand.Foundations.Spectral.OrderedEigenpairs
public import BlockBand.Model.Observables
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Multiplicity-preserving count inversion

For ordered eigenvalues, the rank `i` and the strict count `N(E) = #{j : λ_j < E}` determine each
other (`countBelow_le_rank_iff`, `rank_lt_countBelow_iff`), so a rank deviation forces a count
discrepancy at one of two deterministic energies, and rank-deviation tails are bounded by count
tails and count moments.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.RankLocation

open MeasureTheory

/-- The strict count `#{j : λ_j < E}`, with multiplicities. -/
def countBelow {N : ℕ} (ev : Fin N → ℝ) (E : ℝ) : ℕ :=
  (Finset.univ.filter fun j => ev j < E).card

/-- If the selected value has not crossed E, only earlier ranks can be below E. -/
theorem countBelow_le_rank {N : ℕ} {ev : Fin N → ℝ}
    (hev : Monotone ev) (i : Fin N) {E : ℝ} (hE : E ≤ ev i) :
    countBelow ev E ≤ i.val := by
  unfold countBelow
  calc
    (Finset.univ.filter fun j => ev j < E).card ≤ (Finset.Iio i).card := by
      apply Finset.card_le_card
      intro j hj
      have hjE : ev j < E := (Finset.mem_filter.mp hj).2
      apply Finset.mem_Iio.mpr
      by_contra hji
      have hij : i ≤ j := le_of_not_gt hji
      exact (not_lt_of_ge (hE.trans (hev hij))) hjE
    _ = i.val := Fin.card_Iio i

/-- Crossing the selected value crosses all ranks up to it, with multiplicity. -/
theorem rank_lt_countBelow {N : ℕ} {ev : Fin N → ℝ}
    (hev : Monotone ev) (i : Fin N) {E : ℝ} (hE : ev i < E) :
    i.val < countBelow ev E := by
  have hcard : (Finset.Iic i).card ≤ countBelow ev E := by
    apply Finset.card_le_card
    intro j hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (hev (Finset.mem_Iic.mp hj)).trans_lt hE⟩
  rw [Fin.card_Iic] at hcard
  omega

/-- The equivalence holds also at a repeated eigenvalue and at `E = ev_i`. -/
theorem countBelow_le_rank_iff {N : ℕ} {ev : Fin N → ℝ}
    (hev : Monotone ev) (i : Fin N) (E : ℝ) :
    countBelow ev E ≤ i.val ↔ E ≤ ev i := by
  constructor
  · intro h
    by_contra hE
    exact (not_lt_of_ge h) (rank_lt_countBelow hev i (lt_of_not_ge hE))
  · exact countBelow_le_rank hev i

/-- Strict crossing equivalence in the ascending rank convention. -/
theorem rank_lt_countBelow_iff {N : ℕ} {ev : Fin N → ℝ}
    (hev : Monotone ev) (i : Fin N) (E : ℝ) :
    i.val < countBelow ev E ↔ ev i < E := by
  rw [← not_le, countBelow_le_rank_iff hev i E, not_le]

/-- A rank deviation forces a count discrepancy at one of two deterministic energies. `m` is the
deterministic count centre, typically `N F_sc`; the hypotheses are its lower and upper bulk slopes
around the one-based rank. -/
theorem rank_deviation_forces_count_discrepancy
    {N : ℕ} {ev : Fin N → ℝ} (hev : Monotone ev) (i : Fin N)
    (m : ℝ → ℝ) (e t a : ℝ)
    (hlower : m (e - t) ≤ (i.val + 1 : ℝ) - a)
    (hupper : (i.val + 1 : ℝ) + a ≤ m (e + t))
    (hdev : t < |ev i - e|) :
    a ≤ |(countBelow ev (e - t) : ℝ) - m (e - t)| ∨
      a ≤ |(countBelow ev (e + t) : ℝ) - m (e + t)| := by
  rcases (lt_abs.mp hdev) with hleft | hright
  · right
    have hc : (countBelow ev (e + t) : ℝ) ≤ (i.val : ℝ) := by
      exact_mod_cast countBelow_le_rank hev i (by linarith)
    have habs := neg_le_abs ((countBelow ev (e + t) : ℝ) - m (e + t))
    linarith
  · left
    have hc : (i.val + 1 : ℝ) ≤ (countBelow ev (e - t) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (rank_lt_countBelow hev i (by linarith))
    have habs := le_abs_self ((countBelow ev (e - t) : ℝ) - m (e - t))
    linarith

/-- Count-tail transfer for an arbitrary law `μ`: if the two deterministic count centres straddle
the one-based rank by `a`, the measure of a rank deviation is at most the sum of the two
count-tail measures. -/
theorem measure_rank_deviation_le_count_tails
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (μ : Measure Ω)
    (ev : Ω → Fin N → ℝ) (hev : ∀ ω, Monotone (ev ω)) (i : Fin N)
    (m : ℝ → ℝ) (e t a : ℝ)
    (hlower : m (e - t) ≤ (i.val + 1 : ℝ) - a)
    (hupper : (i.val + 1 : ℝ) + a ≤ m (e + t)) :
    μ {ω | t < |ev ω i - e|} ≤
      μ {ω | a ≤ |(countBelow (ev ω) (e - t) : ℝ) - m (e - t)|} +
      μ {ω | a ≤ |(countBelow (ev ω) (e + t) : ℝ) - m (e + t)|} := by
  calc
    μ {ω | t < |ev ω i - e|} ≤
        μ ({ω | a ≤ |(countBelow (ev ω) (e - t) : ℝ) - m (e - t)|} ∪
          {ω | a ≤ |(countBelow (ev ω) (e + t) : ℝ) - m (e + t)|}) := by
      apply measure_mono
      intro ω hω
      exact rank_deviation_forces_count_discrepancy (hev ω) i m e t a hlower hupper hω
    _ ≤ _ := measure_union_le _ _

/-- The same with the ordering hypothesis only almost everywhere. -/
theorem measure_rank_deviation_le_count_tails_of_ae_monotone
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (μ : Measure Ω)
    (ev : Ω → Fin N → ℝ) (hev : ∀ᵐ ω ∂μ, Monotone (ev ω)) (i : Fin N)
    (m : ℝ → ℝ) (e t a : ℝ)
    (hlower : m (e - t) ≤ (i.val + 1 : ℝ) - a)
    (hupper : (i.val + 1 : ℝ) + a ≤ m (e + t)) :
    μ {ω | t < |ev ω i - e|} ≤
      μ {ω | a ≤ |(countBelow (ev ω) (e - t) : ℝ) - m (e - t)|} +
      μ {ω | a ≤ |(countBelow (ev ω) (e + t) : ℝ) - m (e + t)|} := by
  calc
    _ ≤ μ ({ω | a ≤ |(countBelow (ev ω) (e - t) : ℝ) - m (e - t)|} ∪
        {ω | a ≤ |(countBelow (ev ω) (e + t) : ℝ) - m (e + t)|}) := by
      apply measure_mono_ae
      filter_upwards [hev] with ω hω
      intro hdev
      exact rank_deviation_forces_count_discrepancy hω i m e t a hlower hupper hdev
    _ ≤ _ := measure_union_le _ _

/-- Integer-moment tail inversion, with the ordering only almost everywhere: the threshold power
times the measure of a rank deviation is at most the sum of the two count moments (`ℝ≥0∞`
integrals, so infinite moments are allowed). -/
theorem threshold_pow_mul_measure_rank_deviation_le_count_moments_of_ae_monotone
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (μ : Measure Ω)
    (ev : Ω → Fin N → ℝ) (hev : ∀ᵐ ω ∂μ, Monotone (ev ω)) (i : Fin N)
    (m : ℝ → ℝ) (e t a : ℝ) (q : ℕ)
    (hlower : m (e - t) ≤ (i.val + 1 : ℝ) - a)
    (hupper : (i.val + 1 : ℝ) + a ≤ m (e + t))
    (hmlower : AEMeasurable (fun ω =>
      ENNReal.ofReal |(countBelow (ev ω) (e - t) : ℝ) - m (e - t)| ^ q) μ)
    (hmupper : AEMeasurable (fun ω =>
      ENNReal.ofReal |(countBelow (ev ω) (e + t) : ℝ) - m (e + t)| ^ q) μ) :
    ENNReal.ofReal a ^ q * μ {ω | t < |ev ω i - e|} ≤
      (∫⁻ ω, ENNReal.ofReal |(countBelow (ev ω) (e - t) : ℝ) - m (e - t)| ^ q ∂μ) +
      ∫⁻ ω, ENNReal.ofReal |(countBelow (ev ω) (e + t) : ℝ) - m (e + t)| ^ q ∂μ := by
  have hmarkov (E : ℝ)
      (hm : AEMeasurable (fun ω =>
        ENNReal.ofReal |(countBelow (ev ω) E : ℝ) - m E| ^ q) μ) :
      ENNReal.ofReal a ^ q * μ {ω | a ≤ |(countBelow (ev ω) E : ℝ) - m E|} ≤
        ∫⁻ ω, ENNReal.ofReal |(countBelow (ev ω) E : ℝ) - m E| ^ q ∂μ := by
    calc
      _ ≤ ENNReal.ofReal a ^ q * μ {ω |
          ENNReal.ofReal a ^ q ≤ ENNReal.ofReal |(countBelow (ev ω) E : ℝ) - m E| ^ q} := by
        apply mul_le_mul le_rfl _ (by positivity) (by positivity)
        apply measure_mono
        intro ω hω
        exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal hω) q
      _ ≤ _ := mul_meas_ge_le_lintegral₀ hm _
  calc
    _ ≤ ENNReal.ofReal a ^ q *
        (μ {ω | a ≤ |(countBelow (ev ω) (e - t) : ℝ) - m (e - t)|} +
          μ {ω | a ≤ |(countBelow (ev ω) (e + t) : ℝ) - m (e + t)|}) :=
      mul_le_mul le_rfl (measure_rank_deviation_le_count_tails_of_ae_monotone μ ev hev i m e t a hlower hupper)
        (by positivity) (by positivity)
    _ = _ := mul_add _ _ _
    _ ≤ _ := add_le_add (hmarkov (e - t) hmlower) (hmarkov (e + t) hmupper)

/-- Integer-moment tail inversion: the threshold power times the measure of a rank deviation is at
most the sum of the two count moments (`ℝ≥0∞` integrals, so infinite moments are allowed). -/
theorem threshold_pow_mul_measure_rank_deviation_le_count_moments
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (μ : Measure Ω)
    (ev : Ω → Fin N → ℝ) (hev : ∀ ω, Monotone (ev ω)) (i : Fin N)
    (m : ℝ → ℝ) (e t a : ℝ) (q : ℕ)
    (hlower : m (e - t) ≤ (i.val + 1 : ℝ) - a)
    (hupper : (i.val + 1 : ℝ) + a ≤ m (e + t))
    (hmlower : AEMeasurable (fun ω =>
      ENNReal.ofReal |(countBelow (ev ω) (e - t) : ℝ) - m (e - t)| ^ q) μ)
    (hmupper : AEMeasurable (fun ω =>
      ENNReal.ofReal |(countBelow (ev ω) (e + t) : ℝ) - m (e + t)| ^ q) μ) :
    ENNReal.ofReal a ^ q * μ {ω | t < |ev ω i - e|} ≤
      (∫⁻ ω, ENNReal.ofReal |(countBelow (ev ω) (e - t) : ℝ) - m (e - t)| ^ q ∂μ) +
      ∫⁻ ω, ENNReal.ofReal |(countBelow (ev ω) (e + t) : ℝ) - m (e + t)| ^ q ∂μ :=
  threshold_pow_mul_measure_rank_deviation_le_count_moments_of_ae_monotone
    μ ev (Filter.Eventually.of_forall hev) i m e t a q hlower hupper hmlower hmupper

/-- Specialization to the increasing eigenvalues of a Hermitian matrix. -/
theorem increasingEigenvalue_countBelow_le_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (i : Fin (Fintype.card ι)) (E : ℝ) :
    countBelow (Foundations.Spectral.increasingEigenvalue hH) E ≤ i.val ↔
      E ≤ Foundations.Spectral.increasingEigenvalue hH i :=
  countBelow_le_rank_iff (Foundations.Spectral.increasingEigenvalue_monotone hH) i E

/-- Count-tail transfer for a spectral realization of the physical model at a deterministic rank,
under `model.law` with the ordering `spectral.ordered_ae`. -/
theorem spectralRealization_measure_rank_deviation_le_count_tails
    {p : BlockBand.Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (i : Fin p.N)
    (m : ℝ → ℝ) (e t a : ℝ)
    (hlower : m (e - t) ≤ (i.val + 1 : ℝ) - a)
    (hupper : (i.val + 1 : ℝ) + a ≤ m (e + t)) :
    (model.law : Measure p.SiteMatrix) {H | t < |spectral.eigenvalue H i - e|} ≤
      (model.law : Measure p.SiteMatrix) {H |
        a ≤ |(countBelow (spectral.eigenvalue H) (e - t) : ℝ) - m (e - t)|} +
      (model.law : Measure p.SiteMatrix) {H |
        a ≤ |(countBelow (spectral.eigenvalue H) (e + t) : ℝ) - m (e + t)|} := by
  have horder : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      Monotone (spectral.eigenvalue H) := by
    filter_upwards [spectral.ordered_ae] with H hH
    exact fun i j hij => hH i j hij
  exact measure_rank_deviation_le_count_tails_of_ae_monotone
    (model.law : Measure p.SiteMatrix) spectral.eigenvalue horder i m e t a hlower hupper

end BlockBand.RankLocation
