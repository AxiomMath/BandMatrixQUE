module

public import BlockBand.SourceProcess.FullSourceStops.PolyAlgebra
public import BlockBand.SourceProcess.FullSourceStops.WordValue

/-!
# Evaluating trace polynomials on the path: measurability and a polynomial bound

Every coefficient in the finite contraction rule is bounded by a fixed polynomial in `g` and the
source traces.

* `norm_eval_le`: if every variable `w` of `Ψ` has `|x_w| ≤ M^{|w|}`, `M ≥ 1`, then
  `|Ψ(x)| ≤ polyConst Ψ · M^{polyExp Ψ}` (fixed constants of `Ψ`).
* `measurable_polyValue`: `ω ↦ Ψ(word values at length j)` is measurable for every `Ψ`.
* `ae_norm_polyValue_ord_le`: almost surely, for polynomials in ordinary words,
  `|Ψ(Z_j)| ≤ polyConst Ψ · L_j^{polyExp Ψ}` at every `j` and `k`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory MvPolynomial
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements

variable {nT nI : ℕ}

/-- `Σ_d |coeff_d Ψ|`. -/
def polyConst {σ : Type*} (Ψ : MvPolynomial σ ℂ) : ℝ := ∑ d ∈ Ψ.support, ‖Ψ.coeff d‖

/-- `(max word length of a variable) · totalDegree`. -/
def polyExp (Ψ : TracePoly nT nI) : ℕ := Ψ.vars.sup List.length * Ψ.totalDegree

theorem polyConst_nonneg {σ : Type*} (Ψ : MvPolynomial σ ℂ) : 0 ≤ polyConst Ψ :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_eval_le (Ψ : TracePoly nT nI) (x : TraceWord nT nI → ℂ) {M : ℝ} (hM : 1 ≤ M)
    (hx : ∀ w ∈ Ψ.vars, ‖x w‖ ≤ M ^ w.length) :
    ‖eval x Ψ‖ ≤ polyConst Ψ * M ^ polyExp Ψ := by
  rw [eval_eq, polyConst, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  set L := Ψ.vars.sup List.length
  have hML : 1 ≤ M ^ L := one_le_pow₀ hM
  have hb : ∀ i ∈ d.support, ‖x i‖ ≤ M ^ L := fun i hi => by
    have hv : i ∈ Ψ.vars := (mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩
    exact (hx i hv).trans (pow_le_pow_right₀ hM (Finset.le_sup hv))
  calc ‖∏ i ∈ d.support, x i ^ d i‖ = ∏ i ∈ d.support, ‖x i‖ ^ d i := by
        rw [norm_prod]; simp only [norm_pow]
    _ ≤ ∏ i ∈ d.support, (M ^ L) ^ d i :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i hi =>
          pow_le_pow_left₀ (norm_nonneg _) (hb i hi) _)
    _ = (M ^ L) ^ (∑ i ∈ d.support, d i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (M ^ L) ^ Ψ.totalDegree := pow_le_pow_right₀ hML (le_totalDegree hd)
    _ = M ^ polyExp Ψ := by rw [← pow_mul]; rfl

theorem measurable_eval {α σ : Type*} [MeasurableSpace α] (Ψ : MvPolynomial σ ℂ)
    {x : α → σ → ℂ} (hx : ∀ i, Measurable fun a => x a i) :
    Measurable fun a => eval (x a) Ψ := by
  simp only [eval_eq]
  exact Finset.measurable_sum _ fun d _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => (hx i).pow_const _)

variable {W : ℕ}

theorem measurable_polyValue (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (Ψ : TracePoly nT nI) :
    Measurable fun ω : GrowthPath W => polyValue b E k q W j ω Ψ :=
  measurable_eval Ψ fun w => measurable_wordValue b E k q j w

/-- **Polynomials in ordinary words are bounded by the load**, almost surely. -/
theorem ae_norm_polyValue_ord_le {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (q : Fin nI → ℝ → ℝ) (hq : IsIntervalTests q) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (j : ℕ) (k : Fin nT → ℕ) (Ψ : TracePoly nT nI),
      Ψ ∈ ordPoly nT nI →
        ‖polyValue b E k q W j ω Ψ‖ ≤ polyConst Ψ * wordLoad b E k q W j ω ^ polyExp Ψ := by
  filter_upwards [ae_norm_wordValue_le (nT := nT) hb hE1 hE2 hW q hq,
    ae_scattering_unitary hb hE1 hE2 hW] with ω hω hS j k Ψ hΨ
  exact norm_eval_le Ψ _ (one_le_wordLoad b E k q hq j ω (hS j).2) fun w hw =>
    hω j k w (mem_supported.mp hΨ hw)

theorem one_le_wordLoad_ae {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (q : Fin nI → ℝ → ℝ) (hq : IsIntervalTests q) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (j : ℕ) (k : Fin nT → ℕ), 1 ≤ wordLoad b E k q W j ω := by
  filter_upwards [ae_scattering_unitary hb hE1 hE2 hW] with ω hS j k
  exact one_le_wordLoad b E k q hq j ω (hS j).2

end BlockBand.SourceProcess.FullSourceStops
