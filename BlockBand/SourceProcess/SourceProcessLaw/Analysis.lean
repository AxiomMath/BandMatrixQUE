module

public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Real

/-!
# Two limit-interchange lemmas for the source process theorem

* `exists_limit_of_approx`: if for parameters `c` along a filter `F` the sequence `x_W` is
  eventually within `e(c) → 0` of a convergent sequence `y_c(W) → λ(c)`, then `x` converges and
  `λ(c) → lim x` along `F` (used for `M → ∞` with `e = C/M` and for `s ↓ 0` with `e = Cs`).
* `tendsto_of_iterated`: an `ε`-approximation of `y_W` by `Φ(K,h)` for small `h` and large `K`,
  together with `Φ(·,h) → Λ(h)` and `Λ → Λ'` as `h ↓ 0`, gives `y_W → Λ'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessLaw

open Filter Topology

theorem exists_limit_of_approx {α : Type*} {F : Filter α} [F.NeBot] {x : ℕ → ℝ}
    {y : α → ℕ → ℝ} {lam e : α → ℝ} (he : Tendsto e F (𝓝 0))
    (hy : ∀ᶠ c in F, Tendsto (y c) atTop (𝓝 (lam c)))
    (hxy : ∀ᶠ c in F, ∀ᶠ W in atTop, |x W - y c W| ≤ e c) :
    ∃ L : ℝ, Tendsto x atTop (𝓝 L) ∧ Tendsto lam F (𝓝 L) := by
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hsmall : ∀ᶠ c in F, e c < ε / 4 := he (Iio_mem_nhds (by linarith))
    obtain ⟨c, hc1, hc2, hc3⟩ := (hsmall.and (hy.and hxy)).exists
    have hyc : ∀ᶠ W in atTop, |y c W - lam c| < ε / 4 := by
      have := (Metric.tendsto_nhds.1 hc2) (ε / 4) (by linarith)
      simpa [Real.dist_eq] using this
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hyc.and hc3)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    have h2 := hN N le_rfl
    rw [Real.dist_eq]
    have := abs_sub_le (x n) (lam c) (x N)
    have h3 : |x n - lam c| < ε / 2 := by
      have := abs_sub_le (x n) (y c n) (lam c)
      linarith [h1.1, h1.2]
    have h4 : |x N - lam c| < ε / 2 := by
      have := abs_sub_le (x N) (y c N) (lam c)
      linarith [h2.1, h2.2]
    rw [abs_sub_comm (lam c)] at this
    linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, hL, Metric.tendsto_nhds.2 fun ε hε => ?_⟩
  have hsmall : ∀ᶠ c in F, e c < ε := he (Iio_mem_nhds hε)
  filter_upwards [hsmall, hy, hxy] with c hc1 hc2 hc3
  have hlim : Tendsto (fun W => |x W - y c W|) atTop (𝓝 |L - lam c|) :=
    ((hL.sub hc2).abs)
  have hle : |L - lam c| ≤ e c := le_of_tendsto hlim hc3
  rw [Real.dist_eq, abs_sub_comm]
  linarith

theorem tendsto_of_iterated {y : ℕ → ℝ} {Φ : ℕ → ℝ → ℝ} {Λ : ℝ → ℝ} {Λ' : ℝ}
    (hK : ∀ h, 0 < h → Tendsto (fun K => Φ K h) atTop (𝓝 (Λ h)))
    (hh : Tendsto Λ (𝓝[>] 0) (𝓝 Λ'))
    (hE : ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ᶠ W in atTop, |y W - Φ K h| ≤ ε) :
    Tendsto y atTop (𝓝 Λ') := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨h₀, hh₀, hE'⟩ := hE (ε / 4) (by linarith)
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), (0 < h ∧ h < h₀) ∧ |Λ h - Λ'| < ε / 4 := by
    refine Eventually.and ?_ ?_
    · refine Eventually.and self_mem_nhdsWithin ?_
      exact nhdsWithin_le_nhds (Iio_mem_nhds hh₀)
    · simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 hh) (ε / 4) (by linarith)
  obtain ⟨h, ⟨hpos, hlt⟩, hΛ⟩ := hev.exists
  obtain ⟨K₀, hK₀⟩ := hE' h hpos hlt
  have hKev : ∀ᶠ K in atTop, K₀ ≤ K ∧ |Φ K h - Λ h| < ε / 4 :=
    (eventually_ge_atTop K₀).and
      (by simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 (hK h hpos)) (ε / 4) (by linarith))
  obtain ⟨K, hKle, hΦ⟩ := hKev.exists
  filter_upwards [hK₀ K hKle] with W hW
  rw [Real.dist_eq]
  have h1 := abs_sub_le (y W) (Φ K h) Λ'
  have h2 := abs_sub_le (Φ K h) (Λ h) Λ'
  linarith

end BlockBand.SourceProcess.SourceProcessLaw
