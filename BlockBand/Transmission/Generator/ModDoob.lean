module

public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Modulus of continuity, abstract part I: the martingale part and Doob in `L⁴`

`X : ℕ → Ω → ℝ` is adapted to a filtration `ℱ` and a.s. bounded by `B`. With
`Δ_u = X_{u+1} - X_u` (`modInc`), `m_u = Δ_u - E[Δ_u ∣ ℱ_u]` (`modMart`) and
`N^a_j = Σ_{u<j} m_{a+u}` (`modSum`):

* `condExp_modMart`: `E[m_u ∣ ℱ_u] = 0`; `integral_mul_modMart`: `E[g m_u] = 0` for bounded
  `ℱ_u`-measurable `g` (orthogonality);
* `submartingale_modSum_sq`: `(N^a_j)²` is a submartingale for `j ↦ ℱ_{a+j}`;
* **`meas_modSum_ge_le`** (Doob in `L⁴`): `P(∃ j ≤ n, λ ≤ |N^a_j|) ≤ E(N^a_n)⁴/λ⁴`, from
  Mathlib's `maximal_ineq` applied to `N²` and `N² ≤ N⁴/(2λ²) + λ²/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- `f` is a.e. strongly measurable and a.e. bounded. -/
def ModBdd (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  AEStronglyMeasurable f μ ∧ ∃ C : ℝ, ∀ᵐ ω ∂μ, |f ω| ≤ C

theorem ModBdd.add {f g : Ω → ℝ} (hf : ModBdd μ f) (hg : ModBdd μ g) : ModBdd μ (f + g) := by
  obtain ⟨hf, C, hC⟩ := hf
  obtain ⟨hg, D, hD⟩ := hg
  refine ⟨hf.add hg, C + D, ?_⟩
  filter_upwards [hC, hD] with ω h1 h2
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem ModBdd.neg {f : Ω → ℝ} (hf : ModBdd μ f) : ModBdd μ (-f) := by
  obtain ⟨hf, C, hC⟩ := hf
  exact ⟨hf.neg, C, hC.mono fun ω h => by simpa using h⟩

theorem ModBdd.sub {f g : Ω → ℝ} (hf : ModBdd μ f) (hg : ModBdd μ g) : ModBdd μ (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem ModBdd.mul {f g : Ω → ℝ} (hf : ModBdd μ f) (hg : ModBdd μ g) : ModBdd μ (f * g) := by
  obtain ⟨hf, C, hC⟩ := hf
  obtain ⟨hg, D, hD⟩ := hg
  refine ⟨hf.mul hg, |C| * |D|, ?_⟩
  filter_upwards [hC, hD] with ω h1 h2
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul (h1.trans (le_abs_self _)) (h2.trans (le_abs_self _)) (abs_nonneg _)
    (abs_nonneg _)

theorem ModBdd.pow {f : Ω → ℝ} (hf : ModBdd μ f) (n : ℕ) : ModBdd μ (f ^ n) := by
  induction n with
  | zero => exact ⟨aestronglyMeasurable_const, 1, ae_of_all _ fun _ => by simp⟩
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem ModBdd.const_mul {f : Ω → ℝ} (hf : ModBdd μ f) (c : ℝ) : ModBdd μ (fun ω => c * f ω) :=
  (show ModBdd μ (fun _ => c) from ⟨aestronglyMeasurable_const, |c|, ae_of_all _ fun _ =>
    le_rfl⟩).mul hf

theorem ModBdd.integrable [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : ModBdd μ f) : Integrable f μ := by
  obtain ⟨hf, C, hC⟩ := hf
  exact Integrable.of_bound hf C (hC.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- `Δ_u = X_{u+1} - X_u`. -/
def modInc (X : ℕ → Ω → ℝ) (u : ℕ) : Ω → ℝ := X (u + 1) - X u

/-- `m_u = Δ_u - E[Δ_u ∣ ℱ_u]`. -/
def modMart (μ : Measure Ω) (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (u : ℕ) : Ω → ℝ :=
  modInc X u - μ[modInc X u | ℱ u]

/-- `N^a_j = Σ_{u<j} m_{a+u}`. -/
def modSum (μ : Measure Ω) (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (a j : ℕ) : Ω → ℝ :=
  ∑ u ∈ range j, modMart μ ℱ X (a + u)

/-- The filtration `j ↦ ℱ_{a+j}`. -/
def shiftFiltration (ℱ : Filtration ℕ m0) (a : ℕ) : Filtration ℕ m0 where
  seq j := ℱ (a + j)
  mono' i j h := ℱ.mono (by omega)
  le' j := ℱ.le _

theorem modSum_succ (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (a j : ℕ) :
    modSum μ ℱ X a (j + 1) = modSum μ ℱ X a j + modMart μ ℱ X (a + j) := by
  simp only [modSum, sum_range_succ]

theorem modSum_zero (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (a : ℕ) : modSum μ ℱ X a 0 = 0 := by
  simp [modSum]

section Adapted

variable (ℱ : Filtration ℕ m0) {X : ℕ → Ω → ℝ} (hX : ∀ r, StronglyMeasurable[ℱ r] (X r))
include hX

theorem stronglyMeasurable_modInc (u : ℕ) : StronglyMeasurable[ℱ (u + 1)] (modInc X u) :=
  (hX (u + 1)).sub ((hX u).mono (ℱ.mono (Nat.le_succ u)))

theorem stronglyMeasurable_modMart (u : ℕ) : StronglyMeasurable[ℱ (u + 1)] (modMart μ ℱ X u) :=
  (stronglyMeasurable_modInc ℱ hX u).sub (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_succ u)))

theorem stronglyMeasurable_modSum (a j : ℕ) : StronglyMeasurable[ℱ (a + j)] (modSum μ ℱ X a j) := by
  induction j with
  | zero => rw [modSum_zero]; exact stronglyMeasurable_const
  | succ j ih =>
    rw [modSum_succ]
    exact (ih.mono (ℱ.mono (by omega))).add
      ((stronglyMeasurable_modMart ℱ hX (a + j)).mono (ℱ.mono (by omega)))

variable {B : ℝ} (hB : ∀ r, ∀ᵐ ω ∂μ, |X r ω| ≤ B)
include hB

theorem modBdd_modInc (u : ℕ) : ModBdd μ (modInc X u) := by
  refine ⟨((stronglyMeasurable_modInc ℱ hX u).mono (ℱ.le _)).aestronglyMeasurable, 2 * B, ?_⟩
  filter_upwards [hB u, hB (u + 1)] with ω h0 h1
  simp only [modInc, Pi.sub_apply]
  exact (abs_sub _ _).trans (by linarith)

omit hX in
theorem modBdd_condExp_modInc (u : ℕ) : ModBdd μ (μ[modInc X u | ℱ u]) := by
  refine ⟨(stronglyMeasurable_condExp.mono (ℱ.le _)).aestronglyMeasurable, 2 * B,
    ae_bdd_abs_condExp_of_ae_bdd_abs ?_⟩
  filter_upwards [hB u, hB (u + 1)] with ω h0 h1
  simp only [modInc, Pi.sub_apply]
  exact (abs_sub _ _).trans (by linarith)

theorem modBdd_modMart (u : ℕ) : ModBdd μ (modMart μ ℱ X u) :=
  (modBdd_modInc ℱ hX hB u).sub (modBdd_condExp_modInc ℱ hB u)

theorem modBdd_modSum (a j : ℕ) : ModBdd μ (modSum μ ℱ X a j) := by
  induction j with
  | zero => rw [modSum_zero]; exact ⟨aestronglyMeasurable_const, 0, ae_of_all _ fun _ => by simp⟩
  | succ j ih => rw [modSum_succ]; exact ih.add (modBdd_modMart ℱ hX hB _)

variable [IsFiniteMeasure μ]

/-- `E[m_u ∣ ℱ_u] = 0`. -/
theorem condExp_modMart (u : ℕ) : μ[modMart μ ℱ X u | ℱ u] =ᵐ[μ] 0 := by
  have h1 := (modBdd_modInc ℱ hX hB u).integrable
  have h2 : Integrable (μ[modInc X u | ℱ u]) μ := integrable_condExp
  filter_upwards [condExp_sub h1 h2 (ℱ u),
    condExp_condExp_of_le (μ := μ) (f := modInc X u) le_rfl (ℱ.le u)] with ω e1 e2
  rw [modMart, e1, Pi.sub_apply, e2, sub_self, Pi.zero_apply]

/-- **Orthogonality**: `E[g m_u] = 0` for bounded `ℱ_u`-measurable `g`. -/
theorem integral_mul_modMart (u : ℕ) {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ u] g)
    (hgB : ModBdd μ g) : ∫ ω, g ω * modMart μ ℱ X u ω ∂μ = 0 := by
  have hm := modBdd_modMart ℱ hX hB u
  have hgm : Integrable (g * modMart μ ℱ X u) μ := (hgB.mul hm).integrable
  calc ∫ ω, g ω * modMart μ ℱ X u ω ∂μ = ∫ ω, (μ[g * modMart μ ℱ X u | ℱ u]) ω ∂μ :=
        (integral_condExp (ℱ.le u)).symm
    _ = ∫ ω, (g * μ[modMart μ ℱ X u | ℱ u]) ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hg hgm hm.integrable)
    _ = ∫ _, (0 : ℝ) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [condExp_modMart ℱ hX hB u] with ω h
        rw [Pi.mul_apply, h, Pi.zero_apply, mul_zero]
    _ = 0 := integral_zero _ _

/-- `(N^a_j)²` is a submartingale for `j ↦ ℱ_{a+j}`. -/
theorem submartingale_modSum_sq (a : ℕ) :
    Submartingale (fun j => modSum μ ℱ X a j ^ 2) (shiftFiltration ℱ a) μ := by
  refine submartingale_of_condExp_sub_nonneg_nat (fun j => ?_)
    (fun j => ((modBdd_modSum ℱ hX hB a j).pow 2).integrable) (fun j => ?_)
  · exact (stronglyMeasurable_modSum ℱ hX a j).pow 2
  · have hN := modBdd_modSum ℱ hX hB a j
    have hm := modBdd_modMart ℱ hX hB (a + j)
    have e : modSum μ ℱ X a (j + 1) ^ 2 - modSum μ ℱ X a j ^ 2 =
        (fun ω => 2 * modSum μ ℱ X a j ω) * modMart μ ℱ X (a + j) +
          modMart μ ℱ X (a + j) ^ 2 := by
      funext ω; simp only [modSum_succ, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
      ring
    rw [e]
    have h2N : StronglyMeasurable[ℱ (a + j)] fun ω => 2 * modSum μ ℱ X a j ω :=
      (stronglyMeasurable_modSum ℱ hX a j).const_mul 2
    have i1 : Integrable ((fun ω => 2 * modSum μ ℱ X a j ω) * modMart μ ℱ X (a + j)) μ :=
      ((hN.const_mul 2).mul hm).integrable
    have i2 : Integrable (modMart μ ℱ X (a + j) ^ 2) μ := (hm.pow 2).integrable
    filter_upwards [condExp_add i1 i2 (ℱ (a + j)),
      condExp_mul_of_stronglyMeasurable_left h2N i1 hm.integrable,
      condExp_modMart ℱ hX hB (a + j),
      condExp_nonneg (m := ℱ (a + j)) (μ := μ) (f := modMart μ ℱ X (a + j) ^ 2)
        (ae_of_all _ fun ω => sq_nonneg _)] with ω e1 e2 e3 e4
    show (0 : ℝ) ≤ (μ[_ | ℱ (a + j)]) ω
    rw [e1, Pi.add_apply, e2, Pi.mul_apply, e3, Pi.zero_apply, mul_zero, zero_add]
    exact e4

/-- **Doob's inequality in `L⁴`**: `P(∃ j ≤ n, λ ≤ |N^a_j|) ≤ E(N^a_n)⁴/λ⁴`. -/
theorem meas_modSum_ge_le (a n : ℕ) {l : ℝ} (hl : 0 < l) :
    μ {ω | ∃ j ≤ n, l ≤ |modSum μ ℱ X a j ω|} ≤
      ENNReal.ofReal ((∫ ω, modSum μ ℱ X a n ω ^ 4 ∂μ) / l ^ 4) := by
  set f : ℕ → Ω → ℝ := fun j => modSum μ ℱ X a j ^ 2
  have hsub := submartingale_modSum_sq ℱ hX hB a
  have hnn : 0 ≤ f := fun j ω => sq_nonneg (modSum μ ℱ X a j ω)
  set ε : ℝ≥0 := ⟨l ^ 2, by positivity⟩
  have hmax := maximal_ineq hsub hnn (ε := ε) n
  set A := {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}
  have hsA : {ω | ∃ j ≤ n, l ≤ |modSum μ ℱ X a j ω|} ⊆ A := by
    rintro ω ⟨j, hj, h⟩
    show l ^ 2 ≤ _
    have h1 : l ^ 2 ≤ f j ω := by
      have := pow_le_pow_left₀ hl.le h 2
      rwa [sq_abs] at this
    exact h1.trans (le_sup' (fun k => f k ω) (mem_range.2 (by omega)))
  set N := modSum μ ℱ X a n
  have hNb := modBdd_modSum ℱ hX hB a n
  have hI4 : Integrable (fun ω => N ω ^ 4 / (2 * l ^ 2)) μ := ((hNb.pow 4).integrable).div_const _
  have hI2 : Integrable (f n) μ := (hNb.pow 2).integrable
  have hpt : ∀ ω, f n ω ≤ N ω ^ 4 / (2 * l ^ 2) + l ^ 2 / 2 := fun ω => by
    show N ω ^ 2 ≤ _
    rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (N ω ^ 2 - l ^ 2)]
  have key : ∫ ω in A, f n ω ∂μ ≤ (∫ ω, N ω ^ 4 ∂μ) / (2 * l ^ 2) + l ^ 2 / 2 * μ.real A := by
    calc ∫ ω in A, f n ω ∂μ ≤ ∫ ω in A, (N ω ^ 4 / (2 * l ^ 2) + l ^ 2 / 2) ∂μ :=
          setIntegral_mono hI2.integrableOn (hI4.add (integrable_const _)).integrableOn hpt
      _ = ∫ ω in A, N ω ^ 4 / (2 * l ^ 2) ∂μ + ∫ ω in A, l ^ 2 / 2 ∂μ :=
          integral_add hI4.integrableOn (integrable_const _)
      _ ≤ ∫ ω, N ω ^ 4 / (2 * l ^ 2) ∂μ + l ^ 2 / 2 * μ.real A := by
          rw [setIntegral_const, smul_eq_mul, mul_comm (μ.real A)]
          exact add_le_add_left (setIntegral_le_integral hI4
            (ae_of_all _ fun ω => by positivity)) _
      _ = _ := by rw [integral_div]
  have h1 : ENNReal.ofReal (l ^ 2 * μ.real A) ≤ ENNReal.ofReal (∫ ω in A, f n ω ∂μ) := by
    rw [ENNReal.ofReal_mul (by positivity), measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    convert hmax using 2
    exact (ENNReal.ofReal_coe_nnreal (p := ε))
  have h2 := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun ω => hnn n ω)).1 h1
  have h3 : μ.real A ≤ (∫ ω, N ω ^ 4 ∂μ) / l ^ 4 := by
    have hl2 : 0 < l ^ 2 := by positivity
    rw [le_div_iff₀ (by positivity)]
    have e : (∫ ω, N ω ^ 4 ∂μ) / (2 * l ^ 2) * (2 * l ^ 2) = ∫ ω, N ω ^ 4 ∂μ := by
      field_simp
    nlinarith
  calc μ {ω | ∃ j ≤ n, l ≤ |modSum μ ℱ X a j ω|} ≤ μ A := measure_mono hsA
    _ = ENNReal.ofReal (μ.real A) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h3

end Adapted

end BlockBand.Transmission.Generator
