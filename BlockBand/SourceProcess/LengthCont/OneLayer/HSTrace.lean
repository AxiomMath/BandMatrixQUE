module

public import BlockBand.SourceProcess.LengthCont.OneLayer.FarUpdate
public import BlockBand.SourceProcess.ComplexSourceLaw.Algebra
public import BlockBand.SourceProcess.TagBirth.FreshTrace

/-!
# The near/far blocks of the boundary resolvent have Hilbert–Schmidt norm `g/(4η²)`

For Hermitian paths with invertible path matrix, the squared Hilbert–Schmidt norms of both
off-diagonal blocks of the boundary resolvent `ℝ` equal `g/(4η²)`, with `g` the conductance
(`hs_eq_conductance`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.RawTag BlockBand.SourceProcess.ComplexSourceLaw
open scoped Matrix ComplexOrder ComplexConjugate

variable {W : ℕ}

/-- `Σ_{x,y} |ℝ_{(near,x),(far,y)}|²`. -/
def hs01 (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) : ℝ :=
  ∑ x : Fin W, ∑ y : Fin W, ‖boundaryResolvent b E W n ω (0, x) (1, y)‖ ^ 2

/-- `Σ_{x,y} |ℝ_{(far,y),(near,x)}|²`. -/
def hs10 (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) : ℝ :=
  ∑ x : Fin W, ∑ y : Fin W, ‖boundaryResolvent b E W n ω (1, y) (0, x)‖ ^ 2

theorem hs01_nonneg (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) : 0 ≤ hs01 b E W n ω := by
  unfold hs01; positivity

theorem hs10_nonneg (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) : 0 ≤ hs10 b E W n ω := by
  unfold hs10; positivity

/-- The near block of `ℝ` is `R = (z - X)⁻¹`. -/
theorem portBlock_resolvent (b E : ℝ) (n : ℕ) (ω : GrowthPath W) (hA : ∀ k, (ω.1 k).IsHermitian)
    (hη : 0 < (boundaryZ b E).im) (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)) :
    portBlock (boundaryResolvent b E W n ω) 0 0 = passiveResolvent b E (pathX b E W n ω) := by
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  have hM := isUnit_fullPathMatrix b E n ω hA hη hF
  have h1 := (RawTag.boundary_eqs b E n ω hA hη hF).2
  have h2 := right_eq22 b E n ω hM
  have h3 : (pathPortCoupling (pathAt W n ω))ᴴ * boundaryToInterior b E W n ω =
      1 - boundaryZ b E • boundaryResolvent b E W n ω := by
    rw [boundaryToInterior, boundaryResolvent, ← h2]; abel
  rw [h3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, nearSel_mul_conjTranspose,
    Matrix.mul_smul, Matrix.smul_mul, RawTag.nearSel_mul_mul_conjTranspose] at h1
  have h4 : boundaryZ b E • portBlock (boundaryResolvent b E W n ω) 0 0 =
      boundaryZ b E • passiveResolvent b E (pathX b E W n ω) := by
    have := congrArg (fun M => 1 - M) h1
    simpa using this
  exact smul_right_injective _ hz h4

/-- `R - Rᴴ = (z̄ - z)RᴴR - 2i RᴴYR` for a passive input. -/
theorem resolvent_sub_star_passive (b E : ℝ) (hη : 0 < etaZ b E) (X : Matrix (Fin W) (Fin W) ℂ)
    (hY : (passiveY X).PosSemidef) :
    passiveResolvent b E X - (passiveResolvent b E X)ᴴ =
      (conj (boundaryZ b E) - boundaryZ b E) •
          ((passiveResolvent b E X)ᴴ * passiveResolvent b E X) -
        (2 * Complex.I) • passiveQ b E X := by
  set R := passiveResolvent b E X
  set K := boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  have hKu := (isUnit_iff_isUnit_det _).mp (BlockBand.SourceProcess.TagBirth.isUnit_pencil hη hY)
  have hKR : K * R = 1 := Matrix.mul_nonsing_inv _ hKu
  have e1 : R - Rᴴ = Rᴴ * (Kᴴ - K) * R := by
    have h1 : Rᴴ * Kᴴ = 1 := by rw [← conjTranspose_mul, hKR, conjTranspose_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.one_mul, Matrix.mul_assoc, hKR,
      Matrix.mul_one]
  have e2 : Kᴴ - K = (conj (boundaryZ b E) - boundaryZ b E) • 1 - (2 * Complex.I) • passiveY X := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · simp only [K, passiveY, BlockBand.Transmission.matrixImaginaryPart, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply_eq, Matrix.conjTranspose_apply, Matrix.neg_apply,
        smul_eq_mul, RCLike.star_def, map_sub, map_mul, map_one]
      linear_combination (X i i - (starRingEnd ℂ) (X i i)) * Complex.I_sq
    · simp only [K, passiveY, BlockBand.Transmission.matrixImaginaryPart, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm,
        Matrix.conjTranspose_apply, Matrix.neg_apply, smul_eq_mul, RCLike.star_def, map_sub,
        map_mul, map_zero]
      linear_combination (X i j - (starRingEnd ℂ) (X j i)) * Complex.I_sq
  rw [e1, e2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-- `ℝ - ℝᴴ = (z̄ - z)ℝᴴℝ` (from `𝕊ᴴ𝕊 = 1`). -/
theorem resolvent_sub_star' (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < etaZ b E) :
    boundaryResolvent b E W n ω - (boundaryResolvent b E W n ω)ᴴ =
      (conj (boundaryZ b E) - boundaryZ b E) •
        ((boundaryResolvent b E W n ω)ᴴ * boundaryResolvent b E W n ω) := by
  have h := conjTranspose_mul_scattering b E n ω hA
  set Rb := boundaryResolvent b E W n ω
  set c : ℂ := ((2 * etaZ b E : ℝ) : ℂ) * Complex.I
  have hc : star c = -c := by simp [c]
  have hc0 : c ≠ 0 := by simp [c, hη.ne']
  have hS : scatteringMatrix b E W n ω = 1 - c • Rb := rfl
  rw [hS, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hc] at h
  have h2 : c • (Rbᴴ - Rb - c • (Rbᴴ * Rb)) = 0 := by
    have : (1 - (-c) • Rbᴴ) * (1 - c • Rb) - 1 = c • (Rbᴴ - Rb - c • (Rbᴴ * Rb)) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul]
      module
    rw [← this, h, sub_self]
  have h3 : Rbᴴ - Rb - c • (Rbᴴ * Rb) = 0 := (smul_eq_zero.mp h2).resolve_left hc0
  have hzc : conj (boundaryZ b E) - boundaryZ b E = -c := by
    rw [conj_boundaryZ_sub]; simp [c]
  rw [hzc, neg_smul, ← sub_eq_zero]
  rw [show Rb - Rbᴴ - -(c • (Rbᴴ * Rb)) = -(Rbᴴ - Rb - c • (Rbᴴ * Rb)) by abel, h3, neg_zero]

theorem trace_sq_eq (M : Matrix (Fin W) (Fin W) ℂ) :
    (Mᴴ * M).trace = ((∑ x, ∑ w, ‖M w x‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- The diagonal near trace of `ℝℝᴴ`. -/
theorem nearTrace_mul_star (Rb : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ x : Fin W, (Rb * Rbᴴ) (0, x) (0, x) =
      ((∑ x : Fin W, ∑ w : Fin W, ‖Rb (0, x) (0, w)‖ ^ 2 +
        ∑ x : Fin W, ∑ y : Fin W, ‖Rb (0, x) (1, y)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1 <;> refine Finset.sum_congr rfl fun w _ => ?_ <;>
    rw [RCLike.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq] <;>
    push_cast <;> ring

/-- The diagonal near trace of `ℝᴴℝ`. -/
theorem nearTrace_star_mul (Rb : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ x : Fin W, (Rbᴴ * Rb) (0, x) (0, x) =
      ((∑ x : Fin W, ∑ w : Fin W, ‖Rb (0, w) (0, x)‖ ^ 2 +
        ∑ x : Fin W, ∑ y : Fin W, ‖Rb (1, y) (0, x)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1 <;> refine Finset.sum_congr rfl fun w _ => ?_ <;>
    rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq] <;>
    push_cast <;> ring

/-- The diagonal near trace of `ℝ - ℝᴴ` is the trace of `R - Rᴴ`. -/
theorem nearTrace_sub (Rb : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ x : Fin W, (Rb - Rbᴴ) (0, x) (0, x) = (portBlock Rb 0 0 - (portBlock Rb 0 0)ᴴ).trace := by
  simp [Matrix.trace, portBlock, Matrix.conjTranspose_apply]

/-- **`Re Tr Q = η · hs`** for both off-diagonal blocks (the key identity). -/
theorem hs_eq_mass (b E : ℝ) (n : ℕ) (ω : GrowthPath W) (hA : ∀ k, (ω.1 k).IsHermitian)
    (hη : 0 < (boundaryZ b E).im) (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)) :
    etaZ b E * hs01 b E W n ω = passiveMass b E (pathX b E W n ω) ∧
      etaZ b E * hs10 b E W n ω = passiveMass b E (pathX b E W n ω) := by
  have hη' : 0 < etaZ b E := hη
  have hY := pathNearSchur_passive (κ := fun _ => 0) ⟨hA, fun _ => le_rfl, hη⟩ n
  have hP := portBlock_resolvent b E n ω hA hη hF
  set R := passiveResolvent b E (pathX b E W n ω)
  set Rb := boundaryResolvent b E W n ω
  have hR := resolvent_sub_star_passive b E hη' (pathX b E W n ω) hY
  have htr := congrArg Matrix.trace hR
  simp only [Matrix.trace_sub, Matrix.trace_smul] at htr
  rw [trace_sq_eq] at htr
  have hzc : conj (boundaryZ b E) - boundaryZ b E = -(2 * (etaZ b E : ℂ) * Complex.I) :=
    conj_boundaryZ_sub b E
  have hfro : (∑ x : Fin W, ∑ w : Fin W, ‖R w x‖ ^ 2) =
      ∑ x : Fin W, ∑ w : Fin W, ‖Rb (0, x) (0, w)‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_
    rw [← hP]; rfl
  have hfro' : (∑ x : Fin W, ∑ w : Fin W, ‖R w x‖ ^ 2) =
      ∑ x : Fin W, ∑ w : Fin W, ‖Rb (0, w) (0, x)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_
    rw [← hP]; rfl
  have key : ∀ s : ℝ, (∑ x : Fin W, (Rb - Rbᴴ) (0, x) (0, x) =
      (conj (boundaryZ b E) - boundaryZ b E) *
        ((∑ x : Fin W, ∑ w : Fin W, ‖R w x‖ ^ 2 + s : ℝ) : ℂ)) →
      etaZ b E * s = passiveMass b E (pathX b E W n ω) := by
    intro s hs
    rw [nearTrace_sub, hP, Matrix.trace_sub, htr, hzc] at hs
    simp only [smul_eq_mul] at hs
    push_cast at hs
    have h5 : (passiveQ b E (pathX b E W n ω)).trace = (etaZ b E : ℂ) * s := by
      linear_combination (Complex.I / 2) * hs +
        ((passiveQ b E (pathX b E W n ω)).trace - (etaZ b E : ℂ) * s) * Complex.I_sq
    rw [passiveMass, h5]
    simp
  refine ⟨key _ ?_, key _ ?_⟩
  · have h1 := resolvent_sub_conjTranspose b E n ω hA
    have h2 := congrArg (fun M => ∑ x : Fin W, M (0, x) (0, x)) h1
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h2
    rw [h2, nearTrace_mul_star, hfro, hs01]
  · have h1 := resolvent_sub_star' b E n ω hA hη'
    have h2 := congrArg (fun M => ∑ x : Fin W, M (0, x) (0, x)) h1
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h2
    rw [h2, nearTrace_star_mul, hfro', hs10]

/-- **`hs = g/(4η²)`** for both blocks. -/
theorem hs_eq_conductance (b E : ℝ) (n : ℕ) (ω : GrowthPath W) (hA : ∀ k, (ω.1 k).IsHermitian)
    (hη : 0 < (boundaryZ b E).im) (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)) :
    hs01 b E W n ω = pathConductance b E W n ω / (4 * etaZ b E ^ 2) ∧
      hs10 b E W n ω = pathConductance b E W n ω / (4 * etaZ b E ^ 2) := by
  have hη' : 0 < etaZ b E := hη
  obtain ⟨h1, h2⟩ := hs_eq_mass b E n ω hA hη hF
  have hg : pathConductance b E W n ω = 4 * etaZ b E * passiveMass b E (pathX b E W n ω) := by
    simp only [pathConductance, conductanceOf, pathTransmission, passiveTransmission,
      Matrix.trace_smul, smul_eq_mul, passiveMass, pathX]
    simp [Complex.mul_re]
  rw [hg, ← h1]
  refine ⟨by field_simp, ?_⟩
  rw [h1, ← h2]; field_simp

end BlockBand.SourceProcess.LengthCont.OneLayer
