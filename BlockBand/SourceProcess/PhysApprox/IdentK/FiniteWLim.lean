module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWStop

/-!
# The summed error terms at fixed `W` and `R`

Closed law `μ = closedLaw b W np`. The cubic Taylor terms are at most `η Q_W(R) + η⁻¹ L_W(R)`
(`cube_le`, instead of Cauchy–Schwarz); `Q_W(R)` is bounded through the brackets and `L_W(R)` is
the Lindeberg sum.

* `lint_cube_le`: `∫⁻ 1_A ‖β‖₁³ ≤ η |I| Σ_i ∫⁻ 1_A ‖β_i‖² + η⁻¹ ∫⁻ 1_A ‖β‖₁⁴` (abstract);
* `card_birth_le`: at most `np` steps have a birth;
* `card_Ico_div_le`: `#[⌊W(s+t)⌋, ⌊W(s+t')⌋) / W ≤ t' − t + 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open MeasureTheory Finset Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped ComplexConjugate ENNReal Topology NNReal

/-- **The cubic terms** by `x³ ≤ η x² + x⁴/η` and `‖β‖₁² ≤ |I| Σ_i ‖β_i‖²`. -/
theorem lint_cube_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {I : Type*} [Fintype I]
    {A : Set Ω} (hA : MeasurableSet A) {β : Ω → I → ℂ} (hβ : ∀ i, Measurable fun y => β y i)
    {η : ℝ} (hη : 0 < η) :
    ∫⁻ y, A.indicator (fun y => ENNReal.ofReal (nrm (β y) ^ 3)) y ∂μ ≤
      ENNReal.ofReal η * (ENNReal.ofReal (Fintype.card I : ℝ) *
        ∑ i, ∫⁻ y, A.indicator (fun y => ENNReal.ofReal (‖β y i‖ ^ 2)) y ∂μ) +
      ENNReal.ofReal η⁻¹ * ∫⁻ y, A.indicator (fun y => ENNReal.ofReal (nrm (β y) ^ 4)) y ∂μ := by
  have hn : ∀ y, 0 ≤ nrm (β y) := fun y => nrm_nonneg _
  have hm2 : ∀ i, Measurable fun y => A.indicator (fun y => ENNReal.ofReal (‖β y i‖ ^ 2)) y :=
    fun i => (((hβ i).norm.pow_const 2).ennreal_ofReal).indicator hA
  have hnm : Measurable fun y => nrm (β y) :=
    Finset.measurable_sum _ fun i _ => (hβ i).norm
  have hm4 : Measurable fun y => A.indicator (fun y => ENNReal.ofReal (nrm (β y) ^ 4)) y :=
    ((hnm.pow_const 4).ennreal_ofReal).indicator hA
  have hpt : ∀ y, A.indicator (fun y => ENNReal.ofReal (nrm (β y) ^ 3)) y ≤
      ENNReal.ofReal η * (ENNReal.ofReal (Fintype.card I : ℝ) *
        ∑ i, A.indicator (fun y => ENNReal.ofReal (‖β y i‖ ^ 2)) y) +
      ENNReal.ofReal η⁻¹ * A.indicator (fun y => ENNReal.ofReal (nrm (β y) ^ 4)) y := fun y => by
    by_cases hy : y ∈ A
    · simp only [Set.indicator_of_mem hy]
      have h1 := cube_le (hn y) hη
      have h2 : nrm (β y) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, ‖β y i‖ ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset I)) (f := fun i => ‖β y i‖)
        simpa [nrm] using this
      have h3 : nrm (β y) ^ 3 ≤ η * ((Fintype.card I : ℝ) * ∑ i, ‖β y i‖ ^ 2) +
          η⁻¹ * nrm (β y) ^ 4 := by
        have := mul_le_mul_of_nonneg_left h2 hη.le
        rw [div_eq_inv_mul] at h1
        linarith
      refine (ENNReal.ofReal_le_ofReal h3).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hη.le,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        ENNReal.ofReal_mul (by positivity)]
    · simp [Set.indicator_of_notMem hy]
  calc _ ≤ ∫⁻ y, (ENNReal.ofReal η * (ENNReal.ofReal (Fintype.card I : ℝ) *
        ∑ i, A.indicator (fun y => ENNReal.ofReal (‖β y i‖ ^ 2)) y) +
      ENNReal.ofReal η⁻¹ * A.indicator (fun y => ENNReal.ofReal (nrm (β y) ^ 4)) y) ∂μ :=
        lintegral_mono hpt
    _ = _ := by
      rw [lintegral_add_left ((Finset.measurable_sum _ fun i _ => hm2 i).const_mul _
          |>.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _
          ENNReal.ofReal_ne_top, lintegral_finsetSum _ fun i _ => hm2 i,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem card_birth_le {np : ℕ} (τ : Fin np → ℝ) (W : ℕ) (S : Finset ℕ) :
    (S.filter fun j => IsBirthStep τ W j).card ≤ np := by
  classical
  have h : S.filter (fun j => IsBirthStep τ W j) ⊆ univ.image fun i : Fin np => ⌊(W : ℝ) * τ i⌋₊ :=
    fun j hj => by
      obtain ⟨-, i, hi⟩ := mem_filter.1 hj
      exact mem_image.2 ⟨i, mem_univ _, hi⟩
  exact (card_le_card h).trans (card_image_le.trans (by simp))

theorem card_Ico_div_le {s : ℝ} (hs : 0 ≤ s) {W : ℕ} (hW : 0 < W) {t t' : ℝ≥0} (htt : t ≤ t') :
    (((limLenAll s W t' - limLenAll s W t : ℕ) : ℝ)) / W ≤ (t' : ℝ) - t + 1 := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hnn : limLenAll s W t ≤ limLenAll s W t' :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (by simpa using htt) (Nat.cast_nonneg W))
  rw [Nat.cast_sub hnn, div_le_iff₀ hW']
  have h1 := Nat.floor_le (mul_nonneg hW'.le (by positivity : (0 : ℝ) ≤ s + t'))
  have h2 := Nat.lt_floor_add_one ((W : ℝ) * (s + t))
  simp only [limLenAll] at *
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  nlinarith

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
