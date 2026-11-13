module

public import BlockBand.Transmission.FractionalBulk.Scalar
public import BlockBand.Transmission.Bridge.AlmostSure

/-!
# `Tr X^p` for positive semidefinite `X`: integral representation and a measurable version

* `fracTrace_eq_sum_eigenvalues_psd`: `fracTrace p X = Σ_i λ_i^p` for `X ⪰ 0`;
* `fracTrace_eq_integral_psd`: `Tr X^p = c_p ∫_0^∞ s^{p-1}(n - s Re Tr (X+s)⁻¹) ds` for `X ⪰ 0`
  (`fracTrace_eq_integral`, extended from `X ≻ 0`);
* `fracInt p X`: the right side as a function of an arbitrary matrix, `measurable_fracInt`,
  `fracTrace_eq_fracInt` (`X ⪰ 0`); this gives measurability of `ω ↦ Tr T_r(ω)^p` off a null set;
* `fracTrace_le_card`: `Tr X^p ≤ n` for `0 ⪯ X ⪯ I`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Set Real Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.LawClauses
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fracTrace_nonneg' (p : ℝ) (T : Matrix ι ι ℂ) : 0 ≤ fracTrace p T :=
  Multiset.sum_nonneg fun _ h => by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp h
    exact Real.rpow_nonneg (le_max_right _ _) _

theorem fracTrace_congr' {m : Type*} [Fintype m] [DecidableEq m] {p : ℝ} {A : Matrix ι ι ℂ}
    {B : Matrix m m ℂ} (h : A.charpoly = B.charpoly) : fracTrace p A = fracTrace p B := by
  rw [fracTrace, fracTrace, h]

theorem fracTrace_eq_sum_eigenvalues_psd {X : Matrix ι ι ℂ} (hX : X.PosSemidef) (p : ℝ) :
    fracTrace p X = ∑ i, hX.1.eigenvalues i ^ p := by
  rw [fracTrace, hX.1.roots_charpoly_eq_eigenvalues, Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp [max_eq_left (hX.eigenvalues_nonneg i)]

theorem fracTrace_integrand_eq_psd {X : Matrix ι ι ℂ} (hX : X.PosSemidef) (p : ℝ) {s : ℝ}
    (hs0 : 0 < s) :
    s ^ (p - 1) * ((Fintype.card ι : ℝ) - s * ((X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹).trace.re) =
      ∑ i, s ^ (p - 1) * (hX.1.eigenvalues i / (hX.1.eigenvalues i + s)) := by
  have hev := hX.eigenvalues_nonneg
  have hne : ∀ i, hX.1.eigenvalues i + s ≠ 0 := fun i => by linarith [hev i]
  rw [trace_inv_add_smul_re hX.1 s hne, ← Finset.mul_sum]
  congr 1
  have h : ∀ i, hX.1.eigenvalues i / (hX.1.eigenvalues i + s) =
      1 - s * (hX.1.eigenvalues i + s)⁻¹ := fun i => by
    have := hne i
    field_simp; ring
  simp_rw [h, Finset.sum_sub_distrib, Finset.mul_sum]
  simp

theorem integrableOn_fracTrace_integrand_psd {X : Matrix ι ι ℂ} (hX : X.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    IntegrableOn (fun s : ℝ => s ^ (p - 1) *
      ((Fintype.card ι : ℝ) - s * ((X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹).trace.re)) (Ioi 0) := by
  have h := integrable_finsetSum (μ := volume.restrict (Ioi (0 : ℝ))) Finset.univ fun i _ =>
    integrableOn_rpow_mul_div_add' hp0 hp1 (hX.eigenvalues_nonneg i)
  refine IntegrableOn.congr_fun h (fun s hs => ?_) measurableSet_Ioi
  rw [fracTrace_integrand_eq_psd hX p hs]

/-- **Integral representation** for `X ⪰ 0`. -/
theorem fracTrace_eq_integral_psd {X : Matrix ι ι ℂ} (hX : X.PosSemidef) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) :
    fracTrace p X = cP p * ∫ s in Ioi (0 : ℝ), s ^ (p - 1) *
      ((Fintype.card ι : ℝ) - s * ((X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹).trace.re) := by
  have hev := hX.eigenvalues_nonneg
  rw [fracTrace_eq_sum_eigenvalues_psd hX p]
  simp_rw [rpow_eq_integral' hp0 hp1 (hev _)]
  rw [← Finset.mul_sum, ← integral_finsetSum _ fun i _ =>
    integrableOn_rpow_mul_div_add' hp0 hp1 (hev i)]
  congr 1
  exact (setIntegral_congr_fun measurableSet_Ioi fun s hs =>
    fracTrace_integrand_eq_psd hX p hs).symm

/-- The integral side of `fracTrace_eq_integral_psd` for an arbitrary matrix. -/
def fracInt (p : ℝ) (X : Matrix ι ι ℂ) : ℝ :=
  cP p * ∫ s in Ioi (0 : ℝ), s ^ (p - 1) *
    ((Fintype.card ι : ℝ) - s * ((X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹).trace.re)

theorem fracTrace_eq_fracInt {X : Matrix ι ι ℂ} (hX : X.PosSemidef) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) : fracTrace p X = fracInt p X :=
  fracTrace_eq_integral_psd hX hp0 hp1

theorem measurable_fracInt (p : ℝ) : Measurable (fracInt (ι := ι) p) := by
  have hF : Measurable fun x : Matrix ι ι ℂ × ℝ => x.2 ^ (p - 1) *
      ((Fintype.card ι : ℝ) - x.2 * ((x.1 + (x.2 : ℂ) • (1 : Matrix ι ι ℂ))⁻¹).trace.re) := by
    have hc : Continuous fun x : Matrix ι ι ℂ × ℝ => x.1 + (x.2 : ℂ) • (1 : Matrix ι ι ℂ) :=
      continuous_fst.add ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_const)
    have hinv : Measurable fun x : Matrix ι ι ℂ × ℝ => (x.1 + (x.2 : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ :=
      Bridge.measurable_matrix_inv.comp hc.measurable
    have htr : Measurable fun x : Matrix ι ι ℂ × ℝ =>
        ((x.1 + (x.2 : ℂ) • (1 : Matrix ι ι ℂ))⁻¹).trace.re :=
      Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp hinv)
    exact (measurable_snd.pow_const _).mul (measurable_const.sub (measurable_snd.mul htr))
  have h := (hF.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioi (0 : ℝ)))).measurable
  exact h.const_mul _

/-- `Tr X^p ≤ n` for `0 ⪯ X ⪯ I`, `p > 0`. -/
theorem fracTrace_le_card {X : Matrix ι ι ℂ} (h0 : X.PosSemidef) (h1 : (1 - X).PosSemidef)
    {p : ℝ} (hp0 : 0 < p) : fracTrace p X ≤ Fintype.card ι := by
  have hT := h0.1
  have hev : ∀ i, hT.eigenvalues i ≤ 1 := by
    intro i
    have he := hT.eigenvalues_eq i
    have hp := h1.re_dotProduct_nonneg (hT.eigenvectorBasis i)
    have hn : star (⇑(hT.eigenvectorBasis i)) ⬝ᵥ (⇑(hT.eigenvectorBasis i)) = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hT.eigenvectorBasis.orthonormal.1 i]
      simp
    rw [sub_mulVec, one_mulVec, dotProduct_sub, hn, map_sub] at hp
    simp only [RCLike.one_re] at hp
    have : hT.eigenvalues i = RCLike.re (star (⇑(hT.eigenvectorBasis i)) ⬝ᵥ
        (X *ᵥ ⇑(hT.eigenvectorBasis i))) := he
    linarith
  rw [fracTrace_eq_sum_eigenvalues_psd h0 p]
  calc ∑ i, hT.eigenvalues i ^ p ≤ ∑ _i : ι, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => rpow_le_one (h0.eigenvalues_nonneg i) (hev i) hp0.le
    _ = Fintype.card ι := by simp

end BlockBand.Transmission.FractionalBulk
