module

public import BlockBand.Palm.MomentFlow.MaxStep
public import BlockBand.Palm.MomentFlow.InductionDini

/-!
# The damped maximum principle for the flattened short flow (deterministic)

Data: a short rate path `c(u)` (`c_ij(u) ≥ 0`, `c_ij(u) = 0` if `labelDist i j ≥ ℓ`), a kernel
path `K(u)` with `0 ≤ K_ij(u) ≤ Kmax` and `K_ij(u) ≤ η c_ij(u)` on short pairs, a solution `g`
of the moment flow with rates `c` on the `r`-sector over `[a, b]` with `0 ≤ g(a) ≤ G`, `1 ≤ G`.
A *local window* `P : ℝ → Occ N → Prop` (it may depend on time). At every `u ∈ (a,b)`:

* inside the window (`P u ξ`), at every occupied label `i`: the averaged identity
  `|remSum K(u) g(u) ξ i - V_i(u)(a_ξ Ψ_i(u) + 1 - a_ξ)| ≤ E₁ + ρ(u)`, the averaged law
  `|Σ_j K_ij(u) - V_i(u)| ≤ E₂`, the long kernel bound `longKer ≤ E₃`, the induction hypothesis
  `|Ψ_i(u) - 1| ≤ E₄ + ρ(u)` and `v ≤ V_i(u) ≤ Vb`, `0 < v`;
* outside the window: `|g(u, ξ) - 1| ≤ ρ(u)`.

Here `ρ ≥ 0` is any interval-integrable error that is lower semicontinuous on `(a,b)` (the
integrated error `e_D`; only its time integral is small).

**`flattened_damped`**: for every `u ∈ [a,b]` and every `ξ` in the sector,
`|g(u,ξ) - 1| ≤ G e^{-κ(u-a)} + e/κ + ∫_a^u (C_ρ ρ)`, with `κ = r v/η`,
`e = (r/η)(E₁ + Vb E₄ + G E₂ + r Kmax + (r+1) G E₃)`, `C_ρ = r(1+Vb)/η + κ`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- **Damped two-sided maximum principle for the flattened short flow.** -/
theorem flattened_damped {r ℓ : ℕ} (hr : 1 ≤ r) {c K : ℝ → Fin N → Fin N → ℝ}
    {a b η Kmax G v Vb E₁ E₂ E₃ E₄ : ℝ} (hab : a ≤ b) (hη : 0 < η) (hv : 0 < v)
    (hKm0 : 0 ≤ Kmax) (hG1 : 1 ≤ G) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hE₃ : 0 ≤ E₃) (hE₄ : 0 ≤ E₄)
    (hc0 : ∀ u ∈ Ioo a b, ∀ i j, i ≠ j → 0 ≤ c u i j)
    (hK : ∀ u ∈ Ioo a b, ∀ i j, 0 ≤ K u i j) (hKm : ∀ u ∈ Ioo a b, ∀ i j, K u i j ≤ Kmax)
    (hcK : ∀ u ∈ Ioo a b, ∀ i j, i ≠ j → labelDist i j < ℓ → K u i j ≤ η * c u i j)
    (hcl : ∀ u ∈ Ioo a b, ∀ i j, i ≠ j → ℓ ≤ labelDist i j → c u i j = 0)
    {g : ℝ → Occ N → ℝ} (hg : IsMomentFlowSolution c r a b g)
    (hg0 : ∀ ξ ∈ sector N r, 0 ≤ g a ξ) (hgG : ∀ ξ ∈ sector N r, g a ξ ≤ G)
    {ρ : ℝ → ℝ} (hρi : IntervalIntegrable ρ volume a b)
    (hρl : ∀ u ∈ Ioo a b, LowerSemicontinuousAt ρ u) (hρ0 : ∀ u ∈ Icc a b, 0 ≤ ρ u)
    (P : ℝ → Occ N → Prop) (aR : Occ N → ℝ) (haR : ∀ ξ, 0 ≤ aR ξ ∧ aR ξ ≤ 1)
    (V Ψ : ℝ → Occ N → Fin N → ℝ)
    (hR3 : ∀ u ∈ Ioo a b, ∀ ξ ∈ sector N r, P u ξ → ∀ i, 0 < ξ i →
      |remSum (K u) (g u) ξ i - V u ξ i * (aR ξ * Ψ u ξ i + (1 - aR ξ))| ≤ E₁ + ρ u)
    (hAv : ∀ u ∈ Ioo a b, ∀ ξ ∈ sector N r, P u ξ → ∀ i, 0 < ξ i →
      |∑ j, K u i j - V u ξ i| ≤ E₂)
    (hL : ∀ u ∈ Ioo a b, ∀ ξ ∈ sector N r, P u ξ → ∀ i, 0 < ξ i → longKer (K u) ℓ i ≤ E₃)
    (hIH : ∀ u ∈ Ioo a b, ∀ ξ ∈ sector N r, P u ξ → ∀ i, 0 < ξ i → |Ψ u ξ i - 1| ≤ E₄ + ρ u)
    (hvVb : v ≤ Vb)
    (hV : ∀ u ∈ Ioo a b, ∀ ξ ∈ sector N r, P u ξ → ∀ i, 0 < ξ i → v ≤ V u ξ i ∧ V u ξ i ≤ Vb)
    (hext : ∀ u ∈ Ioo a b, ∀ ξ ∈ sector N r, ¬ P u ξ → |g u ξ - 1| ≤ ρ u) :
    ∀ u ∈ Icc a b, ∀ ξ ∈ sector N r,
      |g u ξ - 1| ≤ G * Real.exp (-((r : ℝ) * v / η) * (u - a)) +
        ((r : ℝ) / η * (E₁ + Vb * E₄ + G * E₂ + r * Kmax + ((r : ℝ) + 1) * G * E₃)) /
          ((r : ℝ) * v / η) +
        ∫ t in a..u, ((r : ℝ) * (1 + Vb) / η + (r : ℝ) * v / η) * ρ t := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set κ := (r : ℝ) * v / η with hκdef
  have hκ : 0 < κ := by positivity
  set e := (r : ℝ) / η * (E₁ + Vb * E₄ + G * E₂ + r * Kmax + ((r : ℝ) + 1) * G * E₃)
  have hVb : 0 ≤ Vb := hv.le.trans hvVb
  set Cρ := (r : ℝ) * (1 + Vb) / η + κ with hCρ
  have hηκ : η * κ = r * v := by rw [hκdef]; field_simp
  have hηe : η * e = r * (E₁ + Vb * E₄ + G * E₂ + r * Kmax + ((r : ℝ) + 1) * G * E₃) := by
    simp only [e]; field_simp
  have hηC : η * Cρ = r * (1 + Vb) + r * v := by
    rw [hCρ, mul_add, hηκ]; congr 1; field_simp
  have he : 0 ≤ e := by
    have : 0 ≤ E₁ + Vb * E₄ + G * E₂ + r * Kmax + ((r : ℝ) + 1) * G * E₃ := by
      have : (0 : ℝ) ≤ G := by linarith
      positivity
    positivity
  have hC0 : 0 ≤ Cρ := by positivity
  have hgpos := hg.ge_of_initial_ge hc0 hg0
  have hgle := hg.le_of_initial_le hc0 hgG
  have hCi : IntervalIntegrable (fun t => Cρ * ρ t) volume a b := hρi.const_mul Cρ
  have hCl : ∀ u ∈ Ioo a b, LowerSemicontinuousAt (fun t => Cρ * ρ t) u := by
    intro u hu
    rcases hC0.lt_or_eq with hpos | hzero
    · have := hρl u hu
      intro y hy
      have hy' : y / Cρ < ρ u := by rw [div_lt_iff₀ hpos]; linarith
      filter_upwards [this (y / Cρ) hy'] with t ht
      have := (div_lt_iff₀ hpos).1 ht
      linarith
    · rw [← hzero]; simp only [zero_mul]; exact lowerSemicontinuousAt_const
  have hC0' : ∀ u ∈ Icc a b, 0 ≤ Cρ * ρ u := fun u hu => mul_nonneg hC0 (hρ0 u hu)
  have hρ0' : ∀ u ∈ Ioo a b, 0 ≤ ρ u := fun u hu => hρ0 u (Ioo_subset_Icc_self hu)
  have hderiv : ∀ x ∈ sector N r, ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => g u x)
      (momentGenerator (c u) (g u) x) (Ioi u) u :=
    fun x hx u hu => ((hg x hx).2 u hu).hasDerivWithinAt
  have hup := dampedMaxPrinciple_lsc (sector N r) (D := fun u ξ => momentGenerator (c u) (g u) ξ)
    hab hκ he (by linarith : (0 : ℝ) ≤ G) hCi hCl hC0' (fun x hx => (hg x hx).1) hderiv
    (fun u hu x hx hmax h1 => by
      show momentGenerator (c u) (g u) x ≤ -κ * (g u x - 1) + e + Cρ * ρ u
      have hu' := Ioo_subset_Icc_self hu
      by_cases hP : P u x
      · have h := maxStep_damped (c := c u) (K := K u) (η := η) (f := g u) hx (hK u hu)
          (hcK u hu) (hcl u hu) (fun ζ hζ => hgpos u hu' ζ hζ) hmax hv.le (haR x).1 (haR x).2
          h1 (hgle u hu' x hx) (hR3 u hu x hx hP) (hAv u hu x hx hP) (hL u hu x hx hP)
          (hIH u hu x hx hP) (hV u hu x hx hP)
        refine le_of_mul_le_mul_left ?_ hη
        have e1 : η * (-κ * (g u x - 1) + e + Cρ * ρ u) =
            -(η * κ) * (g u x - 1) + η * e + (η * Cρ) * ρ u := by ring
        rw [e1, hηκ, hηe, hηC]
        have := hρ0' u hu
        have : 0 ≤ (r : ℝ) * (r * Kmax) := by positivity
        have : 0 ≤ (r : ℝ) * v * ρ u := by positivity
        nlinarith
      · have h0 := momentGenerator_nonpos_of_isMax (hc0 u hu) hx hmax
        have h2 := (abs_le.1 (hext u hu x hx hP)).2
        have : κ * (g u x - 1) ≤ κ * ρ u := mul_le_mul_of_nonneg_left (by linarith) hκ.le
        have : 0 ≤ (r : ℝ) * (1 + Vb) / η * ρ u := by have := hρ0' u hu; positivity
        rw [hCρ]
        nlinarith)
    (fun x hx => by linarith [hgle a ⟨le_rfl, hab⟩ x hx])
  have hlo := dampedMinPrinciple_lsc (sector N r) (D := fun u ξ => momentGenerator (c u) (g u) ξ)
    hab hκ he (by linarith : (0 : ℝ) ≤ G) hCi hCl hC0' (fun x hx => (hg x hx).1) hderiv
    (fun u hu x hx hmin h1 => by
      show κ * (1 - g u x) - e - Cρ * ρ u ≤ momentGenerator (c u) (g u) x
      have hu' := Ioo_subset_Icc_self hu
      by_cases hP : P u x
      · have h := minStep_damped (c := c u) (K := K u) (η := η) (f := g u) hx (hK u hu)
          (hKm u hu) hKm0 (hcK u hu) (hcl u hu) hv.le (haR x).1 (haR x).2
          (fun ζ hζ => hgle u hu' ζ hζ) (hgpos u hu' x hx) h1 hmin
          (hR3 u hu x hx hP) (hAv u hu x hx hP) (hL u hu x hx hP)
          (hIH u hu x hx hP) (hV u hu x hx hP)
        refine le_of_mul_le_mul_left ?_ hη
        have e1 : η * (κ * (1 - g u x) - e - Cρ * ρ u) =
            (η * κ) * (1 - g u x) - η * e - (η * Cρ) * ρ u := by ring
        rw [e1, hηκ, hηe, hηC]
        have := hρ0' u hu
        have : 0 ≤ (r : ℝ) * v * ρ u := by positivity
        have : (r : ℝ) * E₂ ≤ (r : ℝ) * (G * E₂) := by
          have : E₂ ≤ G * E₂ := by nlinarith
          exact mul_le_mul_of_nonneg_left this hr0.le
        nlinarith
      · have h0 := momentGenerator_nonneg_of_isMin (hc0 u hu) hx hmin
        have h2 := (abs_le.1 (hext u hu x hx hP)).1
        have : κ * (1 - g u x) ≤ κ * ρ u := mul_le_mul_of_nonneg_left (by linarith) hκ.le
        have : 0 ≤ (r : ℝ) * (1 + Vb) / η * ρ u := by have := hρ0' u hu; positivity
        rw [hCρ]
        nlinarith)
    (fun x hx => by linarith [hgpos a ⟨le_rfl, hab⟩ x hx])
  intro u hu x hx
  have h1 := hup u hu x hx
  have h2 := hlo u hu x hx
  rw [abs_le]
  constructor <;> linarith

end BlockBand.Palm.MomentFlow
