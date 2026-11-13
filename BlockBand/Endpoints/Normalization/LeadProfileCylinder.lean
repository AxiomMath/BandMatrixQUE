module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Model.Construction.MarkedRotation
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Cylinder functionals are dense in `C(𝒫(𝕋))`

For every `Φ ∈ C_b(𝒫(𝕋))` and `ε > 0` there are `m`, continuous
spatial tests `φ_1, …, φ_m ∈ C(𝕋)` with `‖φ_i‖_∞ ≤ 1` and a continuous `ψ : [-1,1]^m → ℝ` with
`sup_{μ ∈ 𝒫(𝕋)} |Φ(μ) - ψ((∫ φ_i dμ)_i)| ≤ ε` (`exists_cylinder_approx`). The vector
`(∫ φ_i dμ)_i` lies in the cube; it is written with the coordinatewise clamp `projIcc`
(`cylinderVec`), which changes nothing (`cylinderVec_coe`). This is the form used by
`GaussianRatiosContract` (a continuous test on the cube `Fin m → Icc (-1) 1`): on a block-mass
profile `∫ φ_i dν = Σ_k p_k φ_i(k/n)` is a ratio `v*B_iv / v*Dv` with `-D ⪯ B_i ⪯ D`.

**Proof.** Stone–Weierstrass on the compact space `𝒫(𝕋)` (Prokhorov, `CompactSpace
(ProbabilityMeasure 𝕋)` in Mathlib): the cylinder functionals form a subalgebra of
`C(𝒫(𝕋), ℝ)` (concatenate the test families), contain the constants, and separate points
(finite Borel measures on `𝕋` are determined by their continuous integrals).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory
open BlockBand.Model.Construction
open scoped BoundedContinuousFunction

/-- The clamped vector of spatial tests `(∫ φ_i dμ)_i ∈ [-1,1]^m` of a profile. -/
def cylinderVec {m : ℕ} (φ : Fin m → C(Torus, ℝ)) (μ : MassProfile) :
    Fin m → Set.Icc (-1 : ℝ) 1 :=
  fun i => Set.projIcc (-1) 1 (by norm_num) (∫ r, φ i r ∂(μ : Measure Torus))

theorem abs_integral_le_of_abs_le_one (φ : C(Torus, ℝ)) (hφ : ∀ x, |φ x| ≤ 1)
    (μ : MassProfile) : |∫ r, φ r ∂(μ : Measure Torus)| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := (μ : Measure Torus)) (f := fun r => φ r)
    (C := 1) (Filter.Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact hφ r)
  simpa [Real.norm_eq_abs] using h

/-- For tests bounded by one the clamp is idle. -/
theorem cylinderVec_coe {m : ℕ} (φ : Fin m → C(Torus, ℝ)) (hφ : ∀ i x, |φ i x| ≤ 1)
    (μ : MassProfile) (i : Fin m) :
    ((cylinderVec φ μ i : Set.Icc (-1 : ℝ) 1) : ℝ) = ∫ r, φ i r ∂(μ : Measure Torus) := by
  have h := abs_le.mp (abs_integral_le_of_abs_le_one (φ i) (hφ i) μ)
  simp only [cylinderVec, Set.projIcc_of_mem _ ⟨h.1, h.2⟩]

theorem continuous_integral_massProfile (φ : C(Torus, ℝ)) :
    Continuous (fun μ : MassProfile => ∫ r, φ r ∂(μ : Measure Torus)) :=
  continuous_massProfile_integral.comp (continuous_const.prodMk continuous_id)

theorem continuous_cylinderVec {m : ℕ} (φ : Fin m → C(Torus, ℝ)) :
    Continuous (cylinderVec φ) :=
  continuous_pi fun i => continuous_projIcc.comp (continuous_integral_massProfile (φ i))

/-- A cylinder functional `μ ↦ ψ(cylinderVec φ μ)` with tests bounded by one. -/
def IsCylinderFunctional (F : MassProfile → ℝ) : Prop :=
  ∃ (m : ℕ) (φ : Fin m → C(Torus, ℝ)) (ψ : C(Fin m → Set.Icc (-1 : ℝ) 1, ℝ)),
    (∀ i x, |φ i x| ≤ 1) ∧ ∀ μ, F μ = ψ (cylinderVec φ μ)

theorem isCylinderFunctional_const (c : ℝ) : IsCylinderFunctional (fun _ => c) :=
  ⟨0, Fin.elim0, ContinuousMap.const _ c, fun i => Fin.elim0 i, fun _ => rfl⟩

private theorem isCylinderFunctional_binop (op : ℝ → ℝ → ℝ) (hop : Continuous (Function.uncurry op))
    {F G : MassProfile → ℝ} (hF : IsCylinderFunctional F) (hG : IsCylinderFunctional G) :
    IsCylinderFunctional (fun μ => op (F μ) (G μ)) := by
  obtain ⟨m, φ, ψ, hφ, hFψ⟩ := hF
  obtain ⟨m', φ', ψ', hφ', hGψ⟩ := hG
  let φ'' : Fin (m + m') → C(Torus, ℝ) := Fin.append φ φ'
  have hφ'' : ∀ i x, |φ'' i x| ≤ 1 := by
    intro i x
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [φ'', Fin.append_left]; exact hφ j x
    · simp only [φ'', Fin.append_right]; exact hφ' j x
  let L : C(Fin (m + m') → Set.Icc (-1 : ℝ) 1, Fin m → Set.Icc (-1 : ℝ) 1) :=
    ⟨fun x j => x (Fin.castAdd m' j), continuous_pi fun j => continuous_apply _⟩
  let Rr : C(Fin (m + m') → Set.Icc (-1 : ℝ) 1, Fin m' → Set.Icc (-1 : ℝ) 1) :=
    ⟨fun x j => x (Fin.natAdd m j), continuous_pi fun j => continuous_apply _⟩
  let ψ'' : C(Fin (m + m') → Set.Icc (-1 : ℝ) 1, ℝ) :=
    ⟨fun x => op (ψ (L x)) (ψ' (Rr x)),
      hop.comp ((ψ.continuous.comp L.continuous).prodMk (ψ'.continuous.comp Rr.continuous))⟩
  refine ⟨m + m', φ'', ψ'', hφ'', fun μ => ?_⟩
  have hL : L (cylinderVec φ'' μ) = cylinderVec φ μ := by
    funext j; simp only [L, φ'', cylinderVec, ContinuousMap.coe_mk, Fin.append_left]
  have hR : Rr (cylinderVec φ'' μ) = cylinderVec φ' μ := by
    funext j; simp only [Rr, φ'', cylinderVec, ContinuousMap.coe_mk, Fin.append_right]
  change op (F μ) (G μ) = op (ψ (L (cylinderVec φ'' μ))) (ψ' (Rr (cylinderVec φ'' μ)))
  rw [hL, hR, hFψ, hGψ]

theorem IsCylinderFunctional.add {F G : MassProfile → ℝ} (hF : IsCylinderFunctional F)
    (hG : IsCylinderFunctional G) : IsCylinderFunctional (fun μ => F μ + G μ) :=
  isCylinderFunctional_binop (· + ·) continuous_add hF hG

theorem IsCylinderFunctional.mul {F G : MassProfile → ℝ} (hF : IsCylinderFunctional F)
    (hG : IsCylinderFunctional G) : IsCylinderFunctional (fun μ => F μ * G μ) :=
  isCylinderFunctional_binop (· * ·) continuous_mul hF hG

/-- Every single spatial integral is a cylinder functional (rescale the test into the cube). -/
theorem isCylinderFunctional_integral (φ : C(Torus, ℝ)) :
    IsCylinderFunctional (fun μ => ∫ r, φ r ∂(μ : Measure Torus)) := by
  set c : ℝ := ‖φ‖ + 1 with hc
  have hc0 : 0 < c := by positivity
  let φ₁ : Fin 1 → C(Torus, ℝ) := fun _ => c⁻¹ • φ
  have hφ₁ : ∀ i x, |φ₁ i x| ≤ 1 := by
    intro i x
    simp only [φ₁, ContinuousMap.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hc0]
    rw [inv_mul_le_iff₀ hc0, mul_one, ← Real.norm_eq_abs]
    exact (φ.norm_coe_le_norm x).trans (by linarith)
  let ψ : C(Fin 1 → Set.Icc (-1 : ℝ) 1, ℝ) :=
    ⟨fun x => c * (x 0 : ℝ), continuous_const.mul (continuous_subtype_val.comp (continuous_apply 0))⟩
  refine ⟨1, φ₁, ψ, hφ₁, fun μ => ?_⟩
  change _ = c * ((cylinderVec φ₁ μ 0 : Set.Icc (-1 : ℝ) 1) : ℝ)
  rw [cylinderVec_coe φ₁ hφ₁ μ 0]
  simp only [φ₁, ContinuousMap.smul_apply, smul_eq_mul]
  rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]

/-- The subalgebra of cylinder functionals in `C(𝒫(𝕋), ℝ)`. -/
def cylinderSubalgebra : Subalgebra ℝ C(MassProfile, ℝ) where
  carrier := {F | IsCylinderFunctional F}
  mul_mem' hF hG := IsCylinderFunctional.mul hF hG
  add_mem' hF hG := IsCylinderFunctional.add hF hG
  algebraMap_mem' c := isCylinderFunctional_const c

theorem cylinderSubalgebra_separatesPoints : cylinderSubalgebra.SeparatesPoints := by
  intro μ ν hne
  have : BorelSpace Torus := inferInstance
  have hex : ∃ f : Torus →ᵇ ℝ, (∫ r, f r ∂(μ : Measure Torus)) ≠ ∫ r, f r ∂(ν : Measure Torus) := by
    by_contra h
    push Not at h
    exact hne (ProbabilityMeasure.toMeasure_injective
      (ext_of_forall_integral_eq_of_IsFiniteMeasure h))
  obtain ⟨f, hf⟩ := hex
  refine ⟨fun ρ => ∫ r, f.toContinuousMap r ∂(ρ : Measure Torus), ⟨⟨_,
    continuous_integral_massProfile f.toContinuousMap⟩, ?_, rfl⟩, ?_⟩
  · exact isCylinderFunctional_integral f.toContinuousMap
  · exact hf

/-- **Compactness step of the physical lead-profile theorem.** Every bounded continuous functional
on `𝒫(𝕋)` is uniformly within `ε` of a cylinder functional of finitely many continuous spatial
tests bounded by one, with a continuous test on the cube.
-/
theorem exists_cylinder_approx (Φ : MassProfile →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (φ : Fin m → C(Torus, ℝ)) (ψ : C(Fin m → Set.Icc (-1 : ℝ) 1, ℝ)),
      (∀ i x, |φ i x| ≤ 1) ∧ ∀ μ : MassProfile, |Φ μ - ψ (cylinderVec φ μ)| ≤ ε := by
  obtain ⟨⟨g, hg⟩, hgn⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    cylinderSubalgebra cylinderSubalgebra_separatesPoints Φ.toContinuousMap ε hε
  obtain ⟨m, φ, ψ, hφ, hgψ⟩ := (hg : IsCylinderFunctional g)
  refine ⟨m, φ, ψ, hφ, fun μ => ?_⟩
  rw [← hgψ μ, abs_sub_comm]
  have h := ContinuousMap.norm_coe_le_norm (g - Φ.toContinuousMap) μ
  simp only [ContinuousMap.sub_apply, BoundedContinuousFunction.coe_toContinuousMap,
    Real.norm_eq_abs] at h
  exact h.trans hgn.le

end BlockBand.Endpoints.Normalization
