module

public import BlockBand.Transmission.Generator.ModDoob

/-!
# Modulus of continuity, abstract part II: the block fourth moment

* `integral_condExp_pow_four_le`: `E(E[f ∣ m])⁴ ≤ E f⁴` (conditional Jensen through
  `eLpNorm_condExp_le_eLpNorm` at `p = 4`);
* `integral_modMart_pow_four_le`: `E m_u⁴ ≤ 16 E Δ_u⁴`;
* **`integral_modSum_pow_four_le`**: `E Δ_{a+u}⁴ ≤ M` for `u < n` gives `E(N^a_n)⁴ ≤ 320n²M`.
  Recursion `x_{j+1} ≤ (1 + 1/(j+1))x_j + (16j+19)·16M` (orthogonality kills `4N³m`; the other
  cross terms by `4Nm³ ≤ 2N²m² + 2m⁴` and `8N²m² ≤ N⁴/(j+1) + 16(j+1)m⁴`), so no Burkholder
  inequality and no Cauchy–Schwarz are needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

theorem norm_rpow_four (x : ℝ) : ‖x‖ ^ (4 : ℝ) = x ^ 4 := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs,
    Even.pow_abs (by decide)]

theorem ModBdd.memLp [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : ModBdd μ f) (p : ℝ≥0∞) :
    MemLp f p μ := by
  obtain ⟨hf, C, hC⟩ := hf
  exact MemLp.of_bound hf C (hC.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- **Conditional Jensen for `x⁴`.** -/
theorem integral_condExp_pow_four_le [IsFiniteMeasure μ] {m : MeasurableSpace Ω} {f : Ω → ℝ}
    (hf : ModBdd μ f) : ∫ ω, (μ[f | m]) ω ^ 4 ∂μ ≤ ∫ ω, f ω ^ 4 ∂μ := by
  have hfL := hf.memLp 4
  have hcB : ModBdd μ (μ[f | m]) := by
    obtain ⟨-, C, hC⟩ := hf
    exact ⟨integrable_condExp.aestronglyMeasurable, C, ae_bdd_abs_condExp_of_ae_bdd_abs hC⟩
  have hcL := hcB.memLp 4
  have h := eLpNorm_condExp_le_eLpNorm (μ := μ) (m := m) f (p := 4) (by norm_num)
  rw [hcL.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    hfL.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at h
  simp only [ENNReal.toReal_ofNat, norm_rpow_four] at h
  have i0 : 0 ≤ ∫ ω, f ω ^ 4 ∂μ := integral_nonneg fun ω => by positivity
  have i1 : 0 ≤ ∫ ω, (μ[f | m]) ω ^ 4 ∂μ := integral_nonneg fun ω => by positivity
  have h' := (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg i0 _)).1 h
  exact (Real.rpow_le_rpow_iff i1 i0 (by norm_num)).1 h'

theorem sub_pow_four_le (x y : ℝ) : (x - y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h1 : (x - y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x + y)]
  have h2 : (x ^ 2 + y ^ 2) ^ 2 ≤ 2 * (x ^ 4 + y ^ 4) := by nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  have h3 : ((x - y) ^ 2) ^ 2 ≤ (2 * (x ^ 2 + y ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  nlinarith

/-- The pointwise step of the fourth-moment recursion, `c > 0`. -/
theorem add_pow_four_step (N m : ℝ) {c : ℝ} (hc : 0 < c) :
    (N + m) ^ 4 ≤ N ^ 4 + 4 * (N ^ 3 * m) + N ^ 4 / c + (16 * c + 3) * m ^ 4 := by
  have h1 : 6 * N ^ 2 * m ^ 2 + 4 * N * m ^ 3 + m ^ 4 ≤ 8 * N ^ 2 * m ^ 2 + 3 * m ^ 4 := by
    nlinarith [sq_nonneg (m * (N - m))]
  have h2 : 8 * N ^ 2 * m ^ 2 ≤ N ^ 4 / c + 16 * c * m ^ 4 := by
    rw [div_add' _ _ _ hc.ne', le_div_iff₀ hc]
    nlinarith [sq_nonneg (N ^ 2 - 4 * c * m ^ 2)]
  nlinarith

section Adapted

variable [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {X : ℕ → Ω → ℝ}
  (hX : ∀ r, StronglyMeasurable[ℱ r] (X r)) {B : ℝ} (hB : ∀ r, ∀ᵐ ω ∂μ, |X r ω| ≤ B)
include hX hB

theorem integral_modMart_pow_four_le (u : ℕ) {M : ℝ} (h : ∫ ω, modInc X u ω ^ 4 ∂μ ≤ M) :
    ∫ ω, modMart μ ℱ X u ω ^ 4 ∂μ ≤ 16 * M := by
  have hΔ := modBdd_modInc ℱ hX hB u
  have hd := modBdd_condExp_modInc ℱ hB u
  have hJ := integral_condExp_pow_four_le (m := ℱ u) hΔ
  have i1 : Integrable (fun ω => modInc X u ω ^ 4) μ := (hΔ.pow 4).integrable
  have i2 : Integrable (fun ω => (μ[modInc X u | ℱ u]) ω ^ 4) μ := (hd.pow 4).integrable
  have i3 : Integrable (fun ω => modMart μ ℱ X u ω ^ 4) μ := ((hΔ.sub hd).pow 4).integrable
  calc ∫ ω, modMart μ ℱ X u ω ^ 4 ∂μ
      ≤ ∫ ω, 8 * (modInc X u ω ^ 4 + (μ[modInc X u | ℱ u]) ω ^ 4) ∂μ :=
        integral_mono i3 ((i1.add i2).const_mul 8) fun ω => sub_pow_four_le _ _
    _ = 8 * (∫ ω, modInc X u ω ^ 4 ∂μ + ∫ ω, (μ[modInc X u | ℱ u]) ω ^ 4 ∂μ) := by
        rw [integral_const_mul, integral_add i1 i2]
    _ ≤ 16 * M := by linarith

/-- **The block fourth moment**: `E Δ_{a+u}⁴ ≤ M` for `u < n` gives `E(N^a_n)⁴ ≤ 320n²M`. -/
theorem integral_modSum_pow_four_le (a n : ℕ) {M : ℝ}
    (h : ∀ u < n, ∫ ω, modInc X (a + u) ω ^ 4 ∂μ ≤ M) :
    ∫ ω, modSum μ ℱ X a n ω ^ 4 ∂μ ≤ 320 * (n : ℝ) ^ 2 * M := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [modSum_zero]
  have hM : 0 ≤ M := (integral_nonneg fun ω => by positivity).trans (h 0 hn)
  suffices H : ∀ j ≤ n, ∫ ω, modSum μ ℱ X a j ω ^ 4 ∂μ ≤ 20 * (j : ℝ) ^ 2 * (16 * M) by
    have := H n le_rfl; nlinarith
  intro j
  induction j with
  | zero => intro _; simp [modSum_zero]
  | succ j ih =>
    intro hj
    have hx := ih (by omega)
    set x := ∫ ω, modSum μ ℱ X a j ω ^ 4 ∂μ
    have hm4 := integral_modMart_pow_four_le ℱ hX hB (a + j) (h j (by omega))
    have hN := modBdd_modSum ℱ hX hB a j
    have hm := modBdd_modMart ℱ hX hB (a + j)
    have hc : (0 : ℝ) < j + 1 := by positivity
    set c : ℝ := j + 1
    have hO := integral_mul_modMart ℱ hX hB (a + j)
      ((stronglyMeasurable_modSum ℱ hX a j).pow 3) (hN.pow 3)
    have iN : Integrable (fun ω => modSum μ ℱ X a j ω ^ 4) μ := (hN.pow 4).integrable
    have iNm : Integrable (fun ω => modSum μ ℱ X a j ω ^ 3 * modMart μ ℱ X (a + j) ω) μ :=
      ((hN.pow 3).mul hm).integrable
    have im : Integrable (fun ω => modMart μ ℱ X (a + j) ω ^ 4) μ := (hm.pow 4).integrable
    have iS : Integrable (fun ω => modSum μ ℱ X a (j + 1) ω ^ 4) μ := by
      rw [modSum_succ]; exact ((hN.add hm).pow 4).integrable
    have e : modSum μ ℱ X a (j + 1) = modSum μ ℱ X a j + modMart μ ℱ X (a + j) :=
      modSum_succ ℱ X a j
    have hI : ∫ ω, modSum μ ℱ X a (j + 1) ω ^ 4 ∂μ ≤
        ∫ ω, ((1 + 1 / c) * modSum μ ℱ X a j ω ^ 4 +
          4 * (modSum μ ℱ X a j ω ^ 3 * modMart μ ℱ X (a + j) ω) +
          (16 * c + 3) * modMart μ ℱ X (a + j) ω ^ 4) ∂μ := by
      refine integral_mono iS (((iN.const_mul _).add (iNm.const_mul 4)).add (im.const_mul _))
        fun ω => ?_
      have := add_pow_four_step (modSum μ ℱ X a j ω) (modMart μ ℱ X (a + j) ω) hc
      rw [e, Pi.add_apply]
      have e2 : (1 + 1 / c) * modSum μ ℱ X a j ω ^ 4 =
          modSum μ ℱ X a j ω ^ 4 + modSum μ ℱ X a j ω ^ 4 / c := by ring
      linarith
    have k1 : Integrable (fun ω => (1 + 1 / c) * modSum μ ℱ X a j ω ^ 4) μ := iN.const_mul _
    have k2 : Integrable (fun ω => 4 * (modSum μ ℱ X a j ω ^ 3 * modMart μ ℱ X (a + j) ω)) μ :=
      iNm.const_mul _
    have k3 : Integrable (fun ω => (16 * c + 3) * modMart μ ℱ X (a + j) ω ^ 4) μ := im.const_mul _
    have k12 : Integrable (fun ω => (1 + 1 / c) * modSum μ ℱ X a j ω ^ 4 +
        4 * (modSum μ ℱ X a j ω ^ 3 * modMart μ ℱ X (a + j) ω)) μ := k1.add k2
    rw [integral_add k12 k3, integral_add k1 k2, integral_const_mul, integral_const_mul,
      integral_const_mul] at hI
    have hO' : ∫ ω, (modSum μ ℱ X a j ^ 3) ω * modMart μ ℱ X (a + j) ω ∂μ =
        ∫ ω, modSum μ ℱ X a j ω ^ 3 * modMart μ ℱ X (a + j) ω ∂μ := rfl
    rw [← hO', hO, mul_zero, add_zero] at hI
    have hjr : (j : ℝ) ^ 2 / c ≤ j := by
      rw [div_le_iff₀ hc]; simp only [c]; nlinarith
    have hxc : x / c ≤ 20 * j * (16 * M) := by
      calc x / c ≤ 20 * (j : ℝ) ^ 2 * (16 * M) / c := div_le_div_of_nonneg_right hx hc.le
        _ = 20 * ((j : ℝ) ^ 2 / c) * (16 * M) := by ring
        _ ≤ 20 * j * (16 * M) := by gcongr
    have hm4' : (16 * c + 3) * ∫ ω, modMart μ ℱ X (a + j) ω ^ 4 ∂μ ≤ (16 * c + 3) * (16 * M) :=
      mul_le_mul_of_nonneg_left hm4 (by positivity)
    have e3 : (1 + 1 / c) * x = x + x / c := by ring
    push_cast
    simp only [c] at hm4' hxc e3
    nlinarith

end Adapted

end BlockBand.Transmission.Generator
