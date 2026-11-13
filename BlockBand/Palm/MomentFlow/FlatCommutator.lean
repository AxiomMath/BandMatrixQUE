module

public import BlockBand.Palm.MomentFlow.P6Canon
public import BlockBand.Palm.MomentFlow.Flat2Local
public import BlockBand.Palm.MomentFlow.IndProps

/-!
# The flattening commutator along one sample path

`G = U(Av_a H(s))` and `H` are short solutions on `[s,u]`, `a = ramp wd k₀`.

* **`comm_inbulk`**: with the backward row `w` ending at `δ_ξ`,
  `|G(u,ξ) - Av_a H(u)(ξ)| ≤ (M_loc + 1)(2/wd) rR + (M + 1) Σ_{ζ ∉ occBall} w(s,ζ)`
  (pairing plus `flat2_commutator_local`).
* **`comm_far`**: if `a(ξ) = 0` and `a` vanishes off a finite set `S`, then
  `|G(u,ξ) - Av_a H(u)(ξ)| ≤ (M + 1) Σ_{η ∈ S} U δ_η (u, ξ)` (weighted window decomposition).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset

variable {N : ℕ}

theorem IsMomentFlowSolution.const_mul {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {a b : ℝ}
    {F : ℝ → Occ N → ℝ} (hF : IsMomentFlowSolution c r a b F) (k : ℝ) :
    IsMomentFlowSolution c r a b (fun u ξ => k * F u ξ) := by
  intro ξ hξ
  refine ⟨continuousOn_const.mul (hF ξ hξ).1, fun u hu => ?_⟩
  have h := ((hF ξ hξ).2 u hu).const_mul k
  have e : momentGenerator (c u) (fun ζ => k * F u ζ) ξ = k * momentGenerator (c u) (F u) ξ :=
    momentGenerator_smul (c u) k (F u) ξ
  rw [e]; exact h

/-- Pairing with the backward row ending at `δ_ξ`. -/
theorem pair_delta {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ} (hsu : s ≤ u)
    (hsym : ∀ v ∈ Ioo s u, ∀ i j, c v i j = c v j i) {w : ℝ → Occ N → ℝ}
    (hw : IsBackwardMomentFlow c r s u w) {ξ : Occ N} (hξ : ξ ∈ sector N r)
    (hwu : ∀ ζ ∈ sector N r, w u ζ = deltaCfg ξ ζ) {G : ℝ → Occ N → ℝ}
    (hG : IsMomentFlowSolution c r s u G) :
    G u ξ = ∑ ζ ∈ sector N r, w s ζ * G s ζ := by
  rw [hw.represent hsu hsym hG, Finset.sum_congr rfl fun ζ hζ => by rw [hwu ζ hζ]]
  exact (sum_deltaCfg_mul hξ _).symm

/-- **In-bulk commutator.** -/
theorem comm_inbulk {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ} (hsu : s ≤ u)
    (hc : ∀ v ∈ Ioo s u, ∀ i j, i ≠ j → 0 ≤ c v i j)
    (hsym : ∀ v ∈ Ioo s u, ∀ i j, c v i j = c v j i) {w : ℝ → Occ N → ℝ}
    (hw : IsBackwardMomentFlow c r s u w) {ξ : Occ N} (hξ : ξ ∈ sector N r)
    (hwu : ∀ ζ ∈ sector N r, w u ζ = deltaCfg ξ ζ) {G H : ℝ → Occ N → ℝ}
    (hG : IsMomentFlowSolution c r s u G) (hH : IsMomentFlowSolution c r s u H)
    {wd : ℝ} (hwd : 0 < wd) (k₀ : ℕ)
    (hG0 : ∀ ζ ∈ sector N r, G s ζ = avFlat (ramp wd k₀) (H s) ζ)
    {R : ℝ} (hR : 0 ≤ R) {M Mloc : ℝ} (hMloc : 0 ≤ Mloc)
    (hf : ∀ ζ ∈ sector N r, |H s ζ| ≤ M)
    (hfloc : ∀ ζ ∈ sector N r, ζ ∈ occBall r R ξ → ramp wd k₀ ζ ≠ ramp wd k₀ ξ →
      |H s ζ| ≤ Mloc) :
    |G u ξ - avFlat (ramp wd k₀) (H u) ξ| ≤
      (Mloc + 1) * (2 / wd * ((r : ℝ) * R)) +
        (M + 1) * ∑ ζ ∈ sector N r \ occBall r R ξ, w s ζ := by
  have h := flat2_commutator_local hsu hc hsym hw hξ hwu (f := H s) hwd k₀ hR hMloc hf hfloc
  rw [pair_delta hsu hsym hw hξ hwu hG, avFlat, pair_delta hsu hsym hw hξ hwu hH,
    Finset.sum_congr rfl fun ζ hζ => by rw [hG0 ζ hζ, avFlat]]
  exact h

/-- **Far commutator** (`a(ξ) = 0`). -/
theorem comm_far {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ} (hsu : s ≤ u)
    (hc : ∀ v ∈ Ioo s u, ∀ i j, i ≠ j → 0 ≤ c v i j) {G H : ℝ → Occ N → ℝ}
    (hG : IsMomentFlowSolution c r s u G) {wd : ℝ} (k₀ : ℕ)
    (hG0 : ∀ ζ ∈ sector N r, G s ζ = avFlat (ramp wd k₀) (H s) ζ) {M : ℝ}
    (hf : ∀ ζ ∈ sector N r, |H s ζ| ≤ M) (S : Finset (Occ N)) (hSs : S ⊆ sector N r)
    (hS : ∀ ζ ∈ sector N r, ζ ∉ S → ramp wd k₀ ζ = 0) {Φ : Occ N → ℝ → Occ N → ℝ}
    (hΦ : ∀ η ∈ S, IsMomentFlowSolution c r s u (Φ η))
    (hΦ0 : ∀ η ∈ S, ∀ ζ ∈ sector N r, Φ η s ζ = if ζ = η then 1 else 0)
    {ξ : Occ N} (hξ : ξ ∈ sector N r) (hΦnn : ∀ η ∈ S, 0 ≤ Φ η u ξ)
    (hξ0 : ramp wd k₀ ξ = 0) :
    |G u ξ - avFlat (ramp wd k₀) (H u) ξ| ≤ (M + 1) * ∑ η ∈ S, Φ η u ξ := by
  classical
  set α : Occ N → ℝ := fun η => ramp wd k₀ η * (H s η - 1) with hα
  have hG' := hG.sub (isMomentFlowSolution_const c r s u 1)
  have hsum := isMomentFlowSolution_sum S fun η hη => (hΦ η hη).const_mul (α η)
  have heq := hG'.eq_of_initial_eq hc hsum (fun ζ hζ => by
    show G s ζ - 1 = ∑ η ∈ S, α η * Φ η s ζ
    rw [hG0 ζ hζ, avFlat, Finset.sum_congr rfl fun η hη => by rw [hΦ0 η hη ζ hζ]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    by_cases hζS : ζ ∈ S
    · simp only [hζS, ite_true, hα]; ring
    · simp only [hζS, ite_false, hS ζ hζ hζS]; ring) u ⟨hsu, le_rfl⟩ ξ hξ
  replace heq : G u ξ - 1 = ∑ η ∈ S, α η * Φ η u ξ := heq
  have hav : avFlat (ramp wd k₀) (H u) ξ = 1 := by rw [avFlat, hξ0]; ring
  rw [hav, heq, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun η hη => ?_)
  rw [abs_mul, abs_of_nonneg (hΦnn η hη)]
  refine mul_le_mul_of_nonneg_right ?_ (hΦnn η hη)
  have h1 := hf η (hSs hη)
  have h0 := ramp_nonneg wd k₀ η
  have h2 := ramp_le_one wd k₀ η
  rw [hα, abs_mul, abs_of_nonneg h0]
  have h3 : |H s η - 1| ≤ M + 1 := (abs_sub _ _).trans (by simp only [abs_one]; linarith)
  calc ramp wd k₀ η * |H s η - 1| ≤ 1 * (M + 1) :=
        mul_le_mul h2 h3 (abs_nonneg _) zero_le_one
    _ = M + 1 := one_mul _

end BlockBand.Palm.MomentFlow
