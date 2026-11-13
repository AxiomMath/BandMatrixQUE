module

public import BlockBand.Transmission.Generator.ProdFixedAlg

/-!
# Expansion of the finite-`W` tested product into Riemann sums

**`prod_expand`**: with `Y_k = X^k_{r_t} - X^k_{r_s}` (`prodY`) and `a_k(r) = A_k(P_r)` (`prodA`),
`E[Φ(M^W_kM^W_l - Σ_r B(P_r)/W)] = E[ΦY_kY_l] - Σ_r E[ΦY_ka_l(r)]/W - Σ_r E[ΦY_la_k(r)]/W
+ Σ_{r'}(Σ_r E[Φa_l(r')a_k(r)]/W)/W - Σ_r E[ΦB(P_r)]/W` (all sums over `r_s ≤ r < r_t`).
Every term is a (double) Riemann sum of tested power-sum functionals, handled in `ProdConv`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Finset
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal

/-- `Y_k = Tr T^k_{r_t} - Tr T^k_{r_s}`. -/
def prodY (b E' : ℝ) (W j rs rt : ℕ) (ω : GrowthPath W) : ℝ :=
  pathPower b E' W j rt ω - pathPower b E' W j rs ω

/-- `a_j(r) = A_j(P_r)` at `D₀(E)`. -/
def prodA (b E E' : ℝ) (W j r : ℕ) (ω : GrowthPath W) : ℝ :=
  transmissionDrift (transportD0 b E) j (pathPowers b E' W r ω)

/-- `b(r) = B_{kl}(P_r)` at `D₀(E)`. -/
def prodB (b E E' : ℝ) (W k l r : ℕ) (ω : GrowthPath W) : ℝ :=
  transmissionBracket (transportD0 b E) k l (pathPowers b E' W r ω)

theorem ModBdd.div_const' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : ModBdd μ f) (c : ℝ) : ModBdd μ (fun ω => f ω / c) := by
  obtain ⟨C, hC⟩ := hf.2
  refine ⟨by simpa [div_eq_mul_inv] using (hf.1 : AEStronglyMeasurable f μ).mul_const c⁻¹,
    |C| / |c|,
    hC.mono fun ω h => ?_⟩
  rw [abs_div]; exact div_le_div_of_nonneg_right (h.trans (le_abs_self C)) (abs_nonneg c)

theorem modBdd_finsetSum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : ℕ → Ω → ℝ}
    (hf : ∀ r, ModBdd μ (f r)) (s : Finset ℕ) : ModBdd μ (fun ω => ∑ r ∈ s, f r ω) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨aestronglyMeasurable_const, 0, ae_of_all _ fun _ => by simp⟩
  | insert r s hr ih =>
    have : (fun ω => ∑ x ∈ insert r s, f x ω) = f r + fun ω => ∑ x ∈ s, f x ω := by
      funext ω; simp [sum_insert hr]
    rw [this]; exact (hf r).add ih

section Fixed

variable {b E E' : ℝ} (hb : b < 1) (h1 : -2 < E') (h2 : E' < 2) (hD : 0 ≤ transportD0 b E)
  {W : ℕ}
include hb h1 h2 hD

theorem modBdd_prodA (j r : ℕ) : ModBdd (growthPathLaw W b) (prodA b E E' W j r) := by
  refine ⟨((continuous_transmissionDrift (transportD0 b E) j (v := fun x : ℕ → ℝ => x)
    fun i => continuous_apply i).measurable.comp (measurable_pi_iff.mpr fun i =>
      measurable_pathPower b E' i r)).aestronglyMeasurable,
    transportD0 b E * j ^ 2 * (W : ℝ) ^ 2, ?_⟩
  filter_upwards [pathPower_mem (W := W) hb h1 h2] with ω hω
  exact abs_transmissionDrift_le hD j fun i hi _ => by
    obtain ⟨h0, h1, h2⟩ := hω i r hi
    show |pathPower b E' W i r ω| ≤ W
    rw [abs_of_nonneg h0]; exact h1.trans h2

theorem modBdd_prodB {k : ℕ} (hk : 1 ≤ k) (l r : ℕ) :
    ModBdd (growthPathLaw W b) (prodB b E E' W k l r) := by
  refine ⟨((continuous_transmissionBracket (transportD0 b E) k l (v := fun x : ℕ → ℝ => x)
    fun j => continuous_apply j).measurable.comp (measurable_pi_iff.mpr fun j =>
      measurable_pathPower b E' j r)).aestronglyMeasurable, 2 * transportD0 b E * k * l * W, ?_⟩
  filter_upwards [pathPower_bound hb h1 h2 (k := k + l) (by omega) r,
    pathPower_bound hb h1 h2 (k := k + l + 1) (by omega) r] with ω hω1 hω2
  exact abs_transmissionBracket_le hD k l hω1 hω2

/-- **The expansion at one width.** -/
theorem prod_expand {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (rs rt : ℕ) {Φ : GrowthPath W → ℝ}
    (hΦm : Measurable Φ) {B : ℝ} (hB : ∀ ω, |Φ ω| ≤ B) :
    ∫ ω, Φ ω * (prodM b E E' W k rs rt ω * prodM b E E' W l rs rt ω -
        bracketSum b E E' W k l rs rt ω) ∂growthPathLaw W b =
      ∫ ω, Φ ω * (prodY b E' W k rs rt ω * prodY b E' W l rs rt ω) ∂growthPathLaw W b -
        ∑ r ∈ Ico rs rt, (∫ ω, Φ ω * (prodY b E' W k rs rt ω * prodA b E E' W l r ω)
          ∂growthPathLaw W b) / W -
        ∑ r ∈ Ico rs rt, (∫ ω, Φ ω * (prodY b E' W l rs rt ω * prodA b E E' W k r ω)
          ∂growthPathLaw W b) / W +
        ∑ r' ∈ Ico rs rt, (∑ r ∈ Ico rs rt, (∫ ω, Φ ω * (prodA b E E' W l r' ω *
          prodA b E E' W k r ω) ∂growthPathLaw W b) / W) / W -
        ∑ r ∈ Ico rs rt, (∫ ω, Φ ω * prodB b E E' W k l r ω ∂growthPathLaw W b) / W := by
  set μ := growthPathLaw W b
  set I := Ico rs rt
  set S : ℕ → GrowthPath W → ℝ := fun j ω => ∑ r ∈ I, prodA b E E' W j r ω / W
  have hΦb : ∀ᵐ ω ∂μ, ‖Φ ω‖ ≤ B := ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hB ω
  have int : ∀ {f : GrowthPath W → ℝ}, ModBdd μ f → Integrable (fun ω => Φ ω * f ω) μ :=
    fun hf => hf.integrable.bdd_mul hΦm.aestronglyMeasurable hΦb
  have hY : ∀ j, 1 ≤ j → ModBdd μ (prodY b E' W j rs rt) := fun j hj =>
    (modBdd_pathPower hb h1 h2 hj rt).sub (modBdd_pathPower hb h1 h2 hj rs)
  have ha : ∀ j r, ModBdd μ (prodA b E E' W j r) := fun j r => modBdd_prodA hb h1 h2 hD j r
  have hS : ∀ j, ModBdd μ (S j) := fun j =>
    modBdd_finsetSum (fun r => (ha j r).div_const' (W : ℝ)) I
  have hBs : ModBdd μ (fun ω => ∑ r ∈ I, prodB b E E' W k l r ω / W) :=
    modBdd_finsetSum (fun r => (modBdd_prodB hb h1 h2 hD hk l r).div_const' (W : ℝ)) I
  -- pointwise expansion
  have e0 : ∀ ω, Φ ω * (prodM b E E' W k rs rt ω * prodM b E E' W l rs rt ω -
      bracketSum b E E' W k l rs rt ω) =
      Φ ω * (prodY b E' W k rs rt ω * prodY b E' W l rs rt ω) -
        Φ ω * (prodY b E' W k rs rt ω * S l ω) - Φ ω * (prodY b E' W l rs rt ω * S k ω) +
        Φ ω * (S l ω * S k ω) - Φ ω * ∑ r ∈ I, prodB b E E' W k l r ω / W := by
    intro ω
    simp only [prodM, bracketSum, prodY, S, prodA, prodB, I]
    ring
  have i1 := int ((hY k hk).mul (hY l hl))
  have i2 := int ((hY k hk).mul (hS l))
  have i3 := int ((hY l hl).mul (hS k))
  have i4 := int ((hS l).mul (hS k))
  have i5 := int hBs
  have i1' : Integrable (fun ω => Φ ω * (prodY b E' W k rs rt ω * prodY b E' W l rs rt ω)) μ := i1
  have i2' : Integrable (fun ω => Φ ω * (prodY b E' W k rs rt ω * S l ω)) μ := i2
  have i3' : Integrable (fun ω => Φ ω * (prodY b E' W l rs rt ω * S k ω)) μ := i3
  have i4' : Integrable (fun ω => Φ ω * (S l ω * S k ω)) μ := i4
  have i5' : Integrable (fun ω => Φ ω * ∑ r ∈ I, prodB b E E' W k l r ω / W) μ := i5
  have i12 : Integrable (fun ω => Φ ω * (prodY b E' W k rs rt ω * prodY b E' W l rs rt ω) -
      Φ ω * (prodY b E' W k rs rt ω * S l ω)) μ := i1'.sub i2'
  have i123 : Integrable (fun ω => Φ ω * (prodY b E' W k rs rt ω * prodY b E' W l rs rt ω) -
      Φ ω * (prodY b E' W k rs rt ω * S l ω) - Φ ω * (prodY b E' W l rs rt ω * S k ω)) μ :=
    i12.sub i3'
  have i1234 : Integrable (fun ω => Φ ω * (prodY b E' W k rs rt ω * prodY b E' W l rs rt ω) -
      Φ ω * (prodY b E' W k rs rt ω * S l ω) - Φ ω * (prodY b E' W l rs rt ω * S k ω) +
      Φ ω * (S l ω * S k ω)) μ := i123.add i4'
  rw [integral_congr_ae (ae_of_all _ e0), integral_sub i1234 i5', integral_add i123 i4',
    integral_sub i12 i3', integral_sub i1' i2']
  have iYA : ∀ j j' r, 1 ≤ j → Integrable (fun ω =>
      Φ ω * (prodY b E' W j rs rt ω * prodA b E E' W j' r ω) / W) μ := fun j j' r hj =>
    (int ((hY j hj).mul (ha j' r))).div_const _
  have iAA : ∀ r' r, Integrable (fun ω =>
      Φ ω * (prodA b E E' W l r' ω * prodA b E E' W k r ω) / W) μ := fun r' r =>
    (int ((ha l r').mul (ha k r))).div_const _
  have iB : ∀ r, Integrable (fun ω => Φ ω * prodB b E E' W k l r ω / W) μ := fun r =>
    (int (modBdd_prodB hb h1 h2 hD hk l r)).div_const _
  -- the single sums
  have hsum1 : ∀ (j j' : ℕ), 1 ≤ j → ∫ ω, Φ ω * (prodY b E' W j rs rt ω * S j' ω) ∂μ =
      ∑ r ∈ I, (∫ ω, Φ ω * (prodY b E' W j rs rt ω * prodA b E E' W j' r ω) ∂μ) / W := by
    intro j j' hj
    have e : ∀ ω, Φ ω * (prodY b E' W j rs rt ω * S j' ω) =
        ∑ r ∈ I, Φ ω * (prodY b E' W j rs rt ω * prodA b E E' W j' r ω) / W := by
      intro ω; simp only [S, mul_sum]; exact sum_congr rfl fun r _ => by ring
    rw [integral_congr_ae (ae_of_all _ e), integral_finsetSum _ fun r _ => iYA j j' r hj]
    exact sum_congr rfl fun r _ => integral_div _ _
  have hsumB : ∫ ω, Φ ω * ∑ r ∈ I, prodB b E E' W k l r ω / W ∂μ =
      ∑ r ∈ I, (∫ ω, Φ ω * prodB b E E' W k l r ω ∂μ) / W := by
    have e : ∀ ω, Φ ω * ∑ r ∈ I, prodB b E E' W k l r ω / W =
        ∑ r ∈ I, Φ ω * prodB b E E' W k l r ω / W := by
      intro ω; simp only [mul_sum]; exact sum_congr rfl fun r _ => by ring
    rw [integral_congr_ae (ae_of_all _ e), integral_finsetSum _ fun r _ => iB r]
    exact sum_congr rfl fun r _ => integral_div _ _
  have hsum2 : ∫ ω, Φ ω * (S l ω * S k ω) ∂μ = ∑ r' ∈ I, (∑ r ∈ I,
      (∫ ω, Φ ω * (prodA b E E' W l r' ω * prodA b E E' W k r ω) ∂μ) / W) / W := by
    have e : ∀ ω, Φ ω * (S l ω * S k ω) = ∑ r' ∈ I, (∑ r ∈ I,
        Φ ω * (prodA b E E' W l r' ω * prodA b E E' W k r ω) / W) / W := by
      intro ω
      rw [show S l ω * S k ω = ∑ r' ∈ I, ∑ r ∈ I, prodA b E E' W l r' ω / W *
        (prodA b E E' W k r ω / W) from Finset.sum_mul_sum _ _ _ _, mul_sum]
      refine sum_congr rfl fun r' _ => ?_
      rw [mul_sum, sum_div]
      exact sum_congr rfl fun r _ => by ring
    have hin : ∀ r', Integrable (fun ω => ∑ r ∈ I,
        Φ ω * (prodA b E E' W l r' ω * prodA b E E' W k r ω) / W) μ := fun r' =>
      integrable_finsetSum _ fun r _ => iAA r' r
    rw [integral_congr_ae (ae_of_all _ e), integral_finsetSum _ fun r' _ => (hin r').div_const _]
    refine sum_congr rfl fun r' _ => ?_
    rw [integral_div, integral_finsetSum _ fun r _ => iAA r' r]
    congr 1
    exact sum_congr rfl fun r _ => integral_div _ _
  rw [hsum1 k l hk, hsum1 l k hl, hsum2, hsumB]

end Fixed

end BlockBand.Transmission.Generator
