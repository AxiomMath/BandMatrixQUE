module

public import BlockBand.Endpoints.Normalization.LeadProfileCommonPortMeasurable

/-!
# The physical lead-profile theorem: spatial tests of the lead profile as clock ratios

We write the spatial tests of the matched-lead profile as ratios of clocks. With `U = leadResponse b e W r ω` and a weight `w` on the positions
`Fin r ⊕ Fin 2`, `Y(w) = U* diag(w) U` (`weightedClock`, the weight constant on each block):
* `quadForm_weightedClock`: `h*Y(w)h = Σ_x w_x ‖P_x U h‖²` (`leadPositionMass`);
* `weightedClock_isSandwiched`: `|w| ≤ 1` gives `-Y(1) ⪯ Y(w) ⪯ Y(1)`, and `Y(1) ⪰ 0`;
* `weightedClock_trace_pos_or`: `Tr Y(1) > 0` or `U = 0` (then every `Y(w) = 0`);
* `cylinderVec_leadProfile_eq_ratioCube`: for continuous tests `φ_i`, the clamped vector
  `(∫ φ_i dℛ_Jν^lead)_i` is exactly `ratioCube (Y(φ_i(pt_J ·)))_i Y(1) d h` with the constant
  default `d = (φ_i(0))_i`, i.e. the `δ_0` default of `leadProfile` on `h*Y(1)h = 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory Matrix
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ComplexOrder Matrix ComplexConjugate

namespace LeadProfileCommonPort

/-- A position weight spread over the `W` sites of each position. -/
def siteWeight {W r : ℕ} (w : Fin r ⊕ Fin 2 → ℝ) : FullSite W r → ℝ
  | Sum.inl ia => w (Sum.inl ia.1)
  | Sum.inr ja => w (Sum.inr ja.1)

/-- `Y(w) = U* diag(w) U`, `U = leadResponse b e W r ω`. -/
def weightedClock (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) (w : Fin r ⊕ Fin 2 → ℝ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (leadResponse b e W r ω).conjTranspose *
    (Matrix.diagonal (fun s : FullSite W r => ((siteWeight w s : ℝ) : ℂ)) :
      Matrix (FullSite W r) (FullSite W r) ℂ) * leadResponse b e W r ω

theorem leadPositionMass_nonneg (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) (x : Fin r ⊕ Fin 2) : 0 ≤ leadPositionMass b e W r ω h x := by
  rcases x with i | j
  · simp only [leadPositionMass]; positivity
  · simp only [leadPositionMass]; positivity

theorem quadForm_weightedClock (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (w : Fin r ⊕ Fin 2 → ℝ) (h : Fin 2 × Fin W → ℂ) :
    quadForm (weightedClock b e W r ω w) h = ∑ x, w x * leadPositionMass b e W r ω h x := by
  set U := leadResponse b e W r ω with hU
  have h1 : quadForm (weightedClock b e W r ω w) h =
      ∑ s, siteWeight w s * ‖(U *ᵥ h) s‖ ^ 2 := by
    unfold quadForm weightedClock
    rw [← hU, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.star_mulVec]
    simp only [dotProduct, Matrix.mulVec_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have : star ((U *ᵥ h) s) * (((siteWeight w s : ℝ) : ℂ) * (U *ᵥ h) s) =
        ((siteWeight w s * ‖(U *ᵥ h) s‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_left_comm, Complex.star_def, Complex.conj_mul']
      push_cast; ring
    rw [Pi.star_apply, this, Complex.ofReal_re]
  rw [h1, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  simp only [siteWeight, leadPositionMass, Finset.mul_sum, ← hU]

theorem weightedClock_sub (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) (w₁ w₂ : Fin r ⊕ Fin 2 → ℝ) :
    weightedClock b e W r ω w₁ - weightedClock b e W r ω w₂ =
      weightedClock b e W r ω (w₁ - w₂) := by
  unfold weightedClock
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  congr 3
  funext s
  rcases s with s | s <;> simp [siteWeight]

theorem weightedClock_add (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) (w₁ w₂ : Fin r ⊕ Fin 2 → ℝ) :
    weightedClock b e W r ω w₁ + weightedClock b e W r ω w₂ =
      weightedClock b e W r ω (w₁ + w₂) := by
  unfold weightedClock
  rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
  congr 3
  funext s
  rcases s with s | s <;> simp [siteWeight]

theorem weightedClock_posSemidef (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (w : Fin r ⊕ Fin 2 → ℝ) (hw : ∀ x, 0 ≤ w x) : (weightedClock b e W r ω w).PosSemidef := by
  unfold weightedClock
  refine Matrix.PosSemidef.conjTranspose_mul_mul_same ?_ _
  refine Matrix.posSemidef_diagonal_iff.mpr fun s => ?_
  rcases s with s | s <;> simpa [siteWeight] using hw _

theorem weightedClock_isHermitian (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (w : Fin r ⊕ Fin 2 → ℝ) : (weightedClock b e W r ω w).IsHermitian := by
  unfold weightedClock
  refine Matrix.isHermitian_conjTranspose_mul_mul _ ?_
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  ext s
  simp

/-- `|w| ≤ 1` gives `-Y(1) ⪯ Y(w) ⪯ Y(1)`. -/
theorem weightedClock_isSandwiched (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (w : Fin r ⊕ Fin 2 → ℝ) (hw : ∀ x, |w x| ≤ 1) :
    IsSandwichedOn (weightedClock b e W r ω w) (weightedClock b e W r ω (fun _ => 1)) := by
  refine ⟨weightedClock_isHermitian b e W r ω w, ?_, ?_⟩
  · rw [weightedClock_sub]
    refine weightedClock_posSemidef b e W r ω _ fun x => ?_
    simp only [Pi.sub_apply]
    linarith [(abs_le.mp (hw x)).2]
  · rw [weightedClock_add]
    refine weightedClock_posSemidef b e W r ω _ fun x => ?_
    simp only [Pi.add_apply]
    linarith [(abs_le.mp (hw x)).1]

/-- `Tr Y(1) > 0`, or `U = 0`. -/
theorem weightedClock_trace_pos_or (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    0 < (weightedClock b e W r ω (fun _ => 1)).trace.re ∨ leadResponse b e W r ω = 0 := by
  have hY : weightedClock b e W r ω (fun _ => 1) =
      (leadResponse b e W r ω).conjTranspose * leadResponse b e W r ω := by
    unfold weightedClock
    have : (fun s : FullSite W r => ((siteWeight (fun _ => (1 : ℝ)) s : ℝ) : ℂ)) = fun _ => 1 := by
      funext s; rcases s with s | s <;> simp [siteWeight]
    rw [this, Matrix.diagonal_one, Matrix.mul_one]
  by_cases hU : leadResponse b e W r ω = 0
  · exact Or.inr hU
  · left
    have hpsd := (weightedClock_posSemidef b e W r ω (fun _ => 1) fun _ => zero_le_one).trace_nonneg
    have hne : (weightedClock b e W r ω (fun _ => 1)).trace ≠ 0 := by
      rw [hY]; exact fun h => hU (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h)
    have hle := Complex.nonneg_iff.mp hpsd
    rcases lt_or_eq_of_le hle.1 with hlt | heq
    · exact hlt
    · exact absurd (Complex.ext heq.symm hle.2.symm) hne

/-- If `U = 0` every `Y(w)` vanishes. -/
theorem weightedClock_of_zero (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (hU : leadResponse b e W r ω = 0) (w : Fin r ⊕ Fin 2 → ℝ) : weightedClock b e W r ω w = 0 := by
  unfold weightedClock; rw [hU]; simp

/-- **Spatial tests are clock ratios.** For continuous tests `φ_i`, the clamped vector
`(∫ φ_i dℛ_Jν^lead(h))_i` is `ratioCube (Y(φ_i(pt_J ·)))_i Y(1) d h`, with the constant default
`d = (φ_i(0))_i`. -/
theorem cylinderVec_leadProfile_eq_ratioCube {m : ℕ} (φ : Fin m → C(Torus, ℝ)) (b e : ℝ) (n W : ℕ) (ω : GrowthPath W) (h : Fin 2 × Fin W → ℂ)
    (J : ℕ) :
    cylinderVec φ (leadProfile b e n W ω h J) =
      ratioCube (fun i => weightedClock b e W (n - 3) ω (fun x => φ i (leadPt n (n - 3) J x)))
        (weightedClock b e W (n - 3) ω (fun _ => 1)) (fun _ i => φ i 0) h := by
  funext i
  unfold cylinderVec ratioCube
  congr 1
  rw [leadProfile_eq_profileOf, integral_profileOf _ _ _ _
    (leadPositionMass_nonneg b e W (n - 3) ω h) (φ i), quadForm_weightedClock,
    quadForm_weightedClock]
  simp only [one_mul]
  split_ifs with ht
  · rfl
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring

end LeadProfileCommonPort

end BlockBand.Endpoints.Normalization
