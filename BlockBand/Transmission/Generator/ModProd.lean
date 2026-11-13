module

public import BlockBand.Transmission.Generator.ModDoob

/-!
# Products of discrete martingales: orthogonality of increments (input of `ProductMartingaleAlong`)

* `integral_mul_modMart_mul`: `E[Φ m^X_u m^Y_u] = E[Φ Δ^X_uΔ^Y_u] - E[Φ d^X_u d^Y_u]`
  (`d = E[Δ ∣ ℱ_u]`, `Φ` `ℱ_u`-measurable);
* **`integral_mul_modSum_mul`**: `E[Φ N^X_n N^Y_n] = Σ_{u<n} E[Φ m^X_{a+u} m^Y_{a+u}]`
  (the cross terms `E[Φ N^X_j m^Y_{a+j}]` vanish);
* `integral_mul_modSum_mul_eq`: the two combined.

With `modX_eq` (`X_{a+n} - X_a = N^X_n + Σ_{u<n} d^X_{a+u}`), this is the first step towards
`ProductMartingaleAlong`: the finite-`W` product `M^W_k M^W_l` is `N_k N_l` plus terms carrying a
drift error, and `E[Φ N_k N_l] = Σ_r E[Φ(E[Δ^k Δ^l ∣ 𝓕_r] - d^k d^l)]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  (ℱ : Filtration ℕ m0) {X Y : ℕ → Ω → ℝ}
  (hX : ∀ r, StronglyMeasurable[ℱ r] (X r)) (hY : ∀ r, StronglyMeasurable[ℱ r] (Y r))
  {B : ℝ} (hBX : ∀ r, ∀ᵐ ω ∂μ, |X r ω| ≤ B) (hBY : ∀ r, ∀ᵐ ω ∂μ, |Y r ω| ≤ B)
include hX hY hBX hBY

/-- `E[Φ m^X_u m^Y_u] = E[Φ Δ^X_uΔ^Y_u] - E[Φ d^X_u d^Y_u]`. -/
theorem integral_mul_modMart_mul (u : ℕ) {Φ : Ω → ℝ} (hΦ : StronglyMeasurable[ℱ u] Φ)
    (hΦB : ModBdd μ Φ) :
    ∫ ω, Φ ω * (modMart μ ℱ X u ω * modMart μ ℱ Y u ω) ∂μ =
      ∫ ω, Φ ω * (modInc X u ω * modInc Y u ω) ∂μ -
        ∫ ω, Φ ω * ((μ[modInc X u | ℱ u]) ω * (μ[modInc Y u | ℱ u]) ω) ∂μ := by
  have hΔX := modBdd_modInc ℱ hX hBX u
  have hΔY := modBdd_modInc ℱ hY hBY u
  have hdX := modBdd_condExp_modInc ℱ hBX u
  have hdY := modBdd_condExp_modInc ℱ hBY u
  have hmX := modBdd_modMart ℱ hX hBX u
  have smdX : StronglyMeasurable[ℱ u] (μ[modInc X u | ℱ u]) := stronglyMeasurable_condExp
  have smdY : StronglyMeasurable[ℱ u] (μ[modInc Y u | ℱ u]) := stronglyMeasurable_condExp
  -- `E[Φ d^Y m^X] = 0` and `E[Φ d^X m^Y] = 0`
  have o1 := integral_mul_modMart ℱ hX hBX u (hΦ.mul smdY) (hΦB.mul hdY)
  have o2 := integral_mul_modMart ℱ hY hBY u (hΦ.mul smdX) (hΦB.mul hdX)
  have i1 : Integrable (fun ω => Φ ω * (modInc X u ω * modInc Y u ω)) μ :=
    (hΦB.mul (hΔX.mul hΔY)).integrable
  have i2 : Integrable (fun ω => Φ ω * ((μ[modInc X u | ℱ u]) ω * (μ[modInc Y u | ℱ u]) ω)) μ :=
    (hΦB.mul (hdX.mul hdY)).integrable
  have i3 : Integrable (fun ω => (Φ * μ[modInc Y u | ℱ u]) ω * modMart μ ℱ X u ω) μ :=
    ((hΦB.mul hdY).mul hmX).integrable
  have i4 : Integrable (fun ω => (Φ * μ[modInc X u | ℱ u]) ω * modMart μ ℱ Y u ω) μ :=
    ((hΦB.mul hdX).mul (modBdd_modMart ℱ hY hBY u)).integrable
  have e : (fun ω => Φ ω * (modMart μ ℱ X u ω * modMart μ ℱ Y u ω)) =
      fun ω => Φ ω * (modInc X u ω * modInc Y u ω) -
        Φ ω * ((μ[modInc X u | ℱ u]) ω * (μ[modInc Y u | ℱ u]) ω) -
        (Φ * μ[modInc Y u | ℱ u]) ω * modMart μ ℱ X u ω -
        (Φ * μ[modInc X u | ℱ u]) ω * modMart μ ℱ Y u ω := by
    funext ω; simp only [modMart, Pi.sub_apply, Pi.mul_apply]; ring
  have j12 : Integrable (fun ω => Φ ω * (modInc X u ω * modInc Y u ω) -
      Φ ω * ((μ[modInc X u | ℱ u]) ω * (μ[modInc Y u | ℱ u]) ω)) μ := i1.sub i2
  have j123 : Integrable (fun ω => Φ ω * (modInc X u ω * modInc Y u ω) -
      Φ ω * ((μ[modInc X u | ℱ u]) ω * (μ[modInc Y u | ℱ u]) ω) -
      (Φ * μ[modInc Y u | ℱ u]) ω * modMart μ ℱ X u ω) μ := j12.sub i3
  rw [e, integral_sub j123 i4, integral_sub j12 i3, integral_sub i1 i2, o1, o2, sub_zero,
    sub_zero]

/-- **Orthogonality**: `E[Φ N^X_n N^Y_n] = Σ_{u<n} E[Φ m^X_{a+u} m^Y_{a+u}]`, `Φ` `ℱ_a`-measurable. -/
theorem integral_mul_modSum_mul (a n : ℕ) {Φ : Ω → ℝ} (hΦ : StronglyMeasurable[ℱ a] Φ)
    (hΦB : ModBdd μ Φ) :
    ∫ ω, Φ ω * (modSum μ ℱ X a n ω * modSum μ ℱ Y a n ω) ∂μ =
      ∑ u ∈ range n, ∫ ω, Φ ω * (modMart μ ℱ X (a + u) ω * modMart μ ℱ Y (a + u) ω) ∂μ := by
  induction n with
  | zero => simp [modSum_zero]
  | succ j ih =>
    have hNX := modBdd_modSum ℱ hX hBX a j
    have hNY := modBdd_modSum ℱ hY hBY a j
    have hmX := modBdd_modMart ℱ hX hBX (a + j)
    have hmY := modBdd_modMart ℱ hY hBY (a + j)
    have hΦj : StronglyMeasurable[ℱ (a + j)] Φ := hΦ.mono (ℱ.mono (Nat.le_add_right a j))
    have o1 := integral_mul_modMart ℱ hY hBY (a + j)
      (hΦj.mul (stronglyMeasurable_modSum ℱ hX a j)) (hΦB.mul hNX)
    have o2 := integral_mul_modMart ℱ hX hBX (a + j)
      (hΦj.mul (stronglyMeasurable_modSum ℱ hY a j)) (hΦB.mul hNY)
    have i1 : Integrable (fun ω => Φ ω * (modSum μ ℱ X a j ω * modSum μ ℱ Y a j ω)) μ :=
      (hΦB.mul (hNX.mul hNY)).integrable
    have i2 : Integrable (fun ω => (Φ * modSum μ ℱ X a j) ω * modMart μ ℱ Y (a + j) ω) μ :=
      ((hΦB.mul hNX).mul hmY).integrable
    have i3 : Integrable (fun ω => (Φ * modSum μ ℱ Y a j) ω * modMart μ ℱ X (a + j) ω) μ :=
      ((hΦB.mul hNY).mul hmX).integrable
    have i4 : Integrable (fun ω => Φ ω * (modMart μ ℱ X (a + j) ω * modMart μ ℱ Y (a + j) ω)) μ :=
      (hΦB.mul (hmX.mul hmY)).integrable
    have e : (fun ω => Φ ω * (modSum μ ℱ X a (j + 1) ω * modSum μ ℱ Y a (j + 1) ω)) =
        fun ω => Φ ω * (modSum μ ℱ X a j ω * modSum μ ℱ Y a j ω) +
          (Φ * modSum μ ℱ X a j) ω * modMart μ ℱ Y (a + j) ω +
          (Φ * modSum μ ℱ Y a j) ω * modMart μ ℱ X (a + j) ω +
          Φ ω * (modMart μ ℱ X (a + j) ω * modMart μ ℱ Y (a + j) ω) := by
      funext ω; simp only [modSum_succ, Pi.add_apply, Pi.mul_apply]; ring
    have j12 : Integrable (fun ω => Φ ω * (modSum μ ℱ X a j ω * modSum μ ℱ Y a j ω) +
        (Φ * modSum μ ℱ X a j) ω * modMart μ ℱ Y (a + j) ω) μ := i1.add i2
    have j123 : Integrable (fun ω => Φ ω * (modSum μ ℱ X a j ω * modSum μ ℱ Y a j ω) +
        (Φ * modSum μ ℱ X a j) ω * modMart μ ℱ Y (a + j) ω +
        (Φ * modSum μ ℱ Y a j) ω * modMart μ ℱ X (a + j) ω) μ := j12.add i3
    rw [e, integral_add j123 i4, integral_add j12 i3, integral_add i1 i2, o1, o2, ih,
      sum_range_succ]
    ring

/-- **The tested product of the martingale parts.** -/
theorem integral_mul_modSum_mul_eq (a n : ℕ) {Φ : Ω → ℝ} (hΦ : StronglyMeasurable[ℱ a] Φ)
    (hΦB : ModBdd μ Φ) :
    ∫ ω, Φ ω * (modSum μ ℱ X a n ω * modSum μ ℱ Y a n ω) ∂μ =
      ∑ u ∈ range n, (∫ ω, Φ ω * (modInc X (a + u) ω * modInc Y (a + u) ω) ∂μ -
        ∫ ω, Φ ω * ((μ[modInc X (a + u) | ℱ (a + u)]) ω *
          (μ[modInc Y (a + u) | ℱ (a + u)]) ω) ∂μ) := by
  rw [integral_mul_modSum_mul ℱ hX hY hBX hBY a n hΦ hΦB]
  refine sum_congr rfl fun u _ => ?_
  exact integral_mul_modMart_mul ℱ hX hY hBX hBY (a + u)
    (hΦ.mono (ℱ.mono (Nat.le_add_right a u))) hΦB

end BlockBand.Transmission.Generator
