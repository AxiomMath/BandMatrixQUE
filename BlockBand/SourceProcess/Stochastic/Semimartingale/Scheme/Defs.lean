module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Tools
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Riemann
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Scheme.Algebra
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Taylor scheme: data, hypotheses and grid increments

Setting: a probability space `(Ω, m₀, Q)` with an arbitrary filtration
`𝓖 : Filtration ℝ≥0 m₀` (no usual conditions). A process `Z : ℝ≥0 → Ω → ℝ^d` with
`(ω, s)`-dependent characteristics: drift `β_s(ω) ∈ ℝ^d`, covariance `α_s(ω) ∈ ℝ^{d×d}`.

`SchemeHyp Q 𝓖 K Z β α N B Cβ Cα` says: `K` is compact; a.s. `Z` takes values in `K` and has
continuous paths; `Z_t` is `𝓖_t`-a.e.-strongly measurable; `|β| ≤ Cβ`, `|α| ≤ Cα` everywhere;
a.s. `s ↦ β_s(ω)`, `s ↦ α_s(ω)` are Lebesgue-measurable; `N^i` are `𝓖`-martingales with
`N^i_t = Z^i_t - Z^i_0 - ∫_0^t β^i` a.s. for each `t`; `B^{ij}` are `𝓖`-martingales with
`B^{ij}_t = N^i_t N^j_t - ∫_0^t α^{ij}` a.s. for each `t`. No progressive measurability, no
stopping-time property and no completeness of `𝓖` is assumed.

For a grid `t_k = grid s t n k` of `[s, t]` the increments `incN, incI, incJ` (of `N`,
`∫ β`, `∫ α`) and the derivative samples `dφ1, dφ2` at `Z_{t_k}` are defined here.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}

/-- `∫_0^u β^i_v(ω) dv`. -/
def drI (β : ℝ≥0 → Ω → Fin d → ℝ) (i : Fin d) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ v in Ioc (0 : ℝ) u, β v.toNNReal ω i

/-- `∫_0^u α^{ij}_v(ω) dv`. -/
def difJ (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ) (i j : Fin d) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ v in Ioc (0 : ℝ) u, α v.toNNReal ω i j

/-- The generator integrand `Σ β^i ∂_iφ(Z) + ½ Σ α^{ij} ∂_{ij}φ(Z)`. -/
def schemeGen (φ : (Fin d → ℝ) → ℝ) (Z β : ℝ≥0 → Ω → Fin d → ℝ)
    (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, β u ω i * fderiv ℝ φ (Z u ω) (ev i) +
    (1 / 2 : ℝ) * ∑ i, ∑ j, α u ω i j * fderiv ℝ (fderiv ℝ φ) (Z u ω) (ev i) (ev j)

/-- The compensated process `φ(Z_t) - φ(Z_0) - ∫_0^t 𝓛φ`. -/
def schemeProc (φ : (Fin d → ℝ) → ℝ) (Z β : ℝ≥0 → Ω → Fin d → ℝ)
    (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  φ (Z t ω) - φ (Z 0 ω) - ∫ u in Ioc (0 : ℝ) t, schemeGen φ Z β α u.toNNReal ω

/-- Hypotheses of the Taylor scheme (see the module docstring). -/
structure SchemeHyp (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 m₀) (K : Set (Fin d → ℝ))
    (Z β : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ)
    (N : Fin d → ℝ≥0 → Ω → ℝ) (B : Fin d → Fin d → ℝ≥0 → Ω → ℝ) (Cβ Cα : ℝ) : Prop where
  compact : IsCompact K
  mem : ∀ᵐ ω ∂Q, ∀ t, Z t ω ∈ K
  cont : ∀ᵐ ω ∂Q, Continuous fun t => Z t ω
  meas : ∀ t, AEStronglyMeasurable[𝓖 t] (Z t) Q
  driftBound : ∀ t ω i, |β t ω i| ≤ Cβ
  diffBound : ∀ t ω i j, |α t ω i j| ≤ Cα
  driftMeas : ∀ᵐ ω ∂Q, ∀ i, AEStronglyMeasurable (fun u : ℝ => β u.toNNReal ω i) volume
  diffMeas : ∀ᵐ ω ∂Q, ∀ i j, AEStronglyMeasurable (fun u : ℝ => α u.toNNReal ω i j) volume
  mart : ∀ i, Martingale (N i) 𝓖 Q
  mart_eq : ∀ i t, N i t =ᵐ[Q] fun ω => Z t ω i - Z 0 ω i - drI β i t ω
  bracket : ∀ i j, Martingale (B i j) 𝓖 Q
  bracket_eq : ∀ i j t, B i j t =ᵐ[Q] fun ω => N i t ω * N j t ω - difJ α i j t ω

/-!
### Grid increments
-/

/-- Increment of `N^i` over the `k`-th cell. -/
def incN (N : Fin d → ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) (i : Fin d) (k : ℕ) (ω : Ω) : ℝ :=
  N i (grid s t n (k + 1)) ω - N i (grid s t n k) ω

/-- Increment of `∫ β^i` over the `k`-th cell. -/
def incI (β : ℝ≥0 → Ω → Fin d → ℝ) (s t : ℝ≥0) (n : ℕ) (i : Fin d) (k : ℕ) (ω : Ω) : ℝ :=
  drI β i (grid s t n (k + 1)) ω - drI β i (grid s t n k) ω

/-- Increment of `∫ α^{ij}` over the `k`-th cell. -/
def incJ (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ) (s t : ℝ≥0) (n : ℕ) (i j : Fin d) (k : ℕ)
    (ω : Ω) : ℝ :=
  difJ α i j (grid s t n (k + 1)) ω - difJ α i j (grid s t n k) ω

/-- `∂_iφ(Z_{t_k})`. -/
def dφ1 (φ : (Fin d → ℝ) → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (s t : ℝ≥0) (n : ℕ) (i : Fin d)
    (k : ℕ) (ω : Ω) : ℝ :=
  fderiv ℝ φ (Z (grid s t n k) ω) (ev i)

/-- `∂_{ij}φ(Z_{t_k})`. -/
def dφ2 (φ : (Fin d → ℝ) → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (s t : ℝ≥0) (n : ℕ) (i j : Fin d)
    (k : ℕ) (ω : Ω) : ℝ :=
  fderiv ℝ (fderiv ℝ φ) (Z (grid s t n k) ω) (ev i) (ev j)

/-- The discrete martingale transform `Σ_k Σ_i ∂_iφ(Z_{t_k}) (N^i_{t_{k+1}} - N^i_{t_k})`. -/
def transform1 (φ : (Fin d → ℝ) → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (N : Fin d → ℝ≥0 → Ω → ℝ)
    (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ∑ i, dφ1 φ Z s t n i k ω * incN N s t n i k ω

/-- The second-order discrete martingale `Σ_k Σ_{ij} ∂_{ij}φ(Z_{t_k}) (ΔN^i ΔN^j - Δ∫α^{ij})`. -/
def transform2 (φ : (Fin d → ℝ) → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ)
    (N : Fin d → ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ∑ i, ∑ j, dφ2 φ Z s t n i j k ω *
    (incN N s t n i k ω * incN N s t n j k ω - incJ α s t n i j k ω)

/-- Riemann sums for `∫_s^t 𝓛φ`. -/
def riemannSum (φ : (Fin d → ℝ) → ℝ) (Z β : ℝ≥0 → Ω → Fin d → ℝ)
    (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (∑ i, dφ1 φ Z s t n i k ω * incI β s t n i k ω +
    (1 / 2 : ℝ) * ∑ i, ∑ j, dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω)

/-- Cross terms between martingale and drift increments. -/
def crossSum (φ : (Fin d → ℝ) → ℝ) (Z β : ℝ≥0 → Ω → Fin d → ℝ) (N : Fin d → ℝ≥0 → Ω → ℝ)
    (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ∑ i, ∑ j, dφ2 φ Z s t n i j k ω *
    (incN N s t n i k ω * incI β s t n j k ω + incI β s t n i k ω * incN N s t n j k ω +
      incI β s t n i k ω * incI β s t n j k ω)

/-- Sum of Taylor remainders. -/
def remSum (φ : (Fin d → ℝ) → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), taylorRem φ (Z (grid s t n k) ω) (Z (grid s t n (k + 1)) ω)

/-- Sum of squared martingale increments `S_n = Σ_k Σ_i (ΔN^i_k)²`. -/
def sqSum (N : Fin d → ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ∑ i, incN N s t n i k ω ^ 2

/-!
### Elementary pathwise facts
-/

theorem intervalIntegrable_of_bound {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume) {C : ℝ}
    (hC : ∀ u, |f u| ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  refine ⟨?_, ?_⟩ <;>
  exact IntegrableOn.of_bound (by simp) hf.restrict C (ae_of_all _ fun u => by
    rw [Real.norm_eq_abs]; exact hC u)

theorem abs_setIntegral_Ioc_le {f : ℝ → ℝ} {C : ℝ} (hC : ∀ u, |f u| ≤ C) {a : ℝ} (ha : 0 ≤ a) :
    |∫ u in Ioc (0 : ℝ) a, f u| ≤ C * a := by
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) a) (f := f)
    (C := C) (by simp) (fun u _ => by rw [Real.norm_eq_abs]; exact hC u)
  rw [Real.norm_eq_abs] at this
  simpa [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal ha] using this

/-- Increment of a primitive is an interval integral. -/
theorem setIntegral_Ioc_sub {f : ℝ → ℝ} (hf : ∀ a b, IntervalIntegrable f volume a b)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ u in Ioc (0 : ℝ) b, f u) - ∫ u in Ioc (0 : ℝ) a, f u = ∫ u in a..b, f u := by
  rw [← intervalIntegral.integral_of_le (ha.trans hab), ← intervalIntegral.integral_of_le ha,
    intervalIntegral.integral_interval_sub_left (hf 0 b) (hf 0 a)]

theorem abs_intervalIntegral_le {f : ℝ → ℝ} {C : ℝ} (hC : ∀ u, |f u| ≤ C) {a b : ℝ}
    (hab : a ≤ b) : |∫ u in a..b, f u| ≤ C * (b - a) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (E := ℝ) (a := a) (b := b)
    (f := f) (C := C) (fun u _ => by rw [Real.norm_eq_abs]; exact hC u)
  rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ b - a)] at this

theorem norm_ev_le (i : Fin d) : ‖(ev i : Fin d → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = i
  · subst h; simp [ev]
  · simp [ev, h]

theorem abs_clm_ev_le (L : (Fin d → ℝ) →L[ℝ] ℝ) (i : Fin d) : |L (ev i)| ≤ ‖L‖ := by
  rw [← Real.norm_eq_abs]
  have h1 := L.le_opNorm (ev i)
  have h2 : ‖L‖ * ‖(ev i : Fin d → ℝ)‖ ≤ ‖L‖ * 1 :=
    mul_le_mul_of_nonneg_left (norm_ev_le i) (norm_nonneg L)
  linarith

theorem abs_bilin_ev_le (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) (i j : Fin d) :
    |B (ev i) (ev j)| ≤ ‖B‖ := by
  refine (abs_clm_ev_le (B (ev i)) j).trans ?_
  have h1 := B.le_opNorm (ev i)
  have h2 : ‖B‖ * ‖(ev i : Fin d → ℝ)‖ ≤ ‖B‖ * 1 :=
    mul_le_mul_of_nonneg_left (norm_ev_le i) (norm_nonneg B)
  linarith

end BlockBand.SourceProcess.Stochastic.Semimartingale
