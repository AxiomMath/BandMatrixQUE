module

public import BlockBand.SourceProcess.LengthCont.OneLayer.Coords

/-!
# The exact one-layer increment of the source data

`incTerm b E r Δ ℝ a_i a_k c_i c_k d_i d_k e_i e_k` is the increment of the unit-mass entry
`(i, k)` of component `r` of `(𝒦, M_pr, B_pr, J_pr)`, as a function of the length-`n` frames and
of the fresh `Δ`. A.s. on `probedPathLaw`, for every length `n ≥ 1` at which both probes are
born, `complexSourceData (n+1) r i k - complexSourceData n r i k = μ_{ik} · incTerm …`
(`ae_incr_eq`).
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
open BlockBand.Internal.Contracts.CoareaPalm
open scoped Matrix ComplexOrder ComplexConjugate

variable {W : ℕ}

/-- The fresh far shift `w_y = conj(a*Δℝ₀₁(·,y))` of `d`. -/
def shiftL (Δ : Matrix (Fin W) (Fin W) ℂ) (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (a : Fin W → ℂ) : Fin W → ℂ :=
  fun y => star (bilinear a Δ (fun x => R (0, x) (1, y)))

/-- The fresh far shift `v_y = (ℝ₁₀Δc)_y` of `e`. -/
def shiftR (Δ : Matrix (Fin W) (Fin W) ℂ) (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (c : Fin W → ℂ) : Fin W → ℂ :=
  fun y => bilinear (fun x => star (R (1, y) (0, x))) Δ c

/-- Increment of `gramOf` under `u ↦ u + s`, `v ↦ v + t`. -/
def gramInc (u v s t : Fin W → ℂ) : ℂ := gramOf u t + gramOf s v + gramOf s t

theorem gramOf_add (u v s t : Fin W → ℂ) :
    gramOf (u + s) (v + t) = gramOf u v + gramInc u v s t := by
  simp only [gramOf, gramInc, Pi.add_apply, star_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **The unit-mass increment** of component `r`, entry `(i, k)`. -/
def incTerm (b E : ℝ) (r : Fin 4) (Δ : Matrix (Fin W) (Fin W) ℂ)
    (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (aI aK cI cK dI dK eI eK : Fin W → ℂ) : ℂ :=
  let T1 := (bilinear aI Δ cK - star (bilinear aK Δ cI)) /
    (conj (boundaryZ b E) - boundaryZ b E)
  let dFd := gramInc dI dK (shiftL Δ R aI) (shiftL Δ R aK)
  let dFe := gramInc eI eK (shiftR Δ R cI) (shiftR Δ R cK)
  ![bilinear aI Δ cK, T1, T1 - dFd, dFd - dFe] r

theorem incTerm_two (b E : ℝ) (Δ : Matrix (Fin W) (Fin W) ℂ)
    (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (aI aK cI cK dI dK eI eK : Fin W → ℂ) :
    incTerm b E 2 Δ R aI aK cI cK dI dK eI eK =
      (bilinear aI Δ cK - star (bilinear aK Δ cI)) / (conj (boundaryZ b E) - boundaryZ b E) -
        gramInc dI dK (shiftL Δ R aI) (shiftL Δ R aK) := rfl

theorem incTerm_three (b E : ℝ) (Δ : Matrix (Fin W) (Fin W) ℂ)
    (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (aI aK cI cK dI dK eI eK : Fin W → ℂ) :
    incTerm b E 3 Δ R aI aK cI cK dI dK eI eK =
      gramInc dI dK (shiftL Δ R aI) (shiftL Δ R aK) -
        gramInc eI eK (shiftR Δ R cI) (shiftR Δ R cK) := rfl

theorem massF_symm {np : ℕ} (m : Fin np → ℝ) (i k : Fin np) : massF m k i = massF m i k := by
  simp only [massF, mul_comm]

theorem star_massF {np : ℕ} (m : Fin np → ℝ) (i k : Fin np) : star (massF m i k) = massF m i k := by
  simp [massF]

/-- The frames of the probes at a sample, as the arguments of `incTerm`. -/
def incAt {np : ℕ} (b E : ℝ) (W n : ℕ) (τ : Fin np → ℝ) (r : Fin 4) (i k : Fin np)
    (x : ProbedPath W np) : ℂ :=
  incTerm b E r (stepDelta b E W n x.1) (boundaryResolvent b E W n x.1)
    (nearL b E W n (birth W τ i) x.1 (x.2 i)) (nearL b E W n (birth W τ k) x.1 (x.2 k))
    (nearR b E W n (birth W τ i) x.1 (x.2 i)) (nearR b E W n (birth W τ k) x.1 (x.2 k))
    (farL b E W n (birth W τ i) x.1 (x.2 i)) (farL b E W n (birth W τ k) x.1 (x.2 k))
    (farR b E W n (birth W τ i) x.1 (x.2 i)) (farR b E W n (birth W τ k) x.1 (x.2 k))

/-- **The exact increment, a.s.** -/
theorem ae_incr_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {W : ℕ} (hW : 1 ≤ W) {np : ℕ} (τ m : Fin np → ℝ) (hm : ∀ j, 0 ≤ m j) :
    ∀ᵐ x ∂probedPathLaw W np b, ∀ n : ℕ, 1 ≤ n → ∀ i k : Fin np, birth W τ i < n →
      birth W τ k < n → ∀ r : Fin 4,
        complexSourceData b E W (n + 1) τ m x r i k - complexSourceData b E W n τ m x r i k =
          massF m i k * incAt b E W n τ r i k x := by
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  have hη' : 0 < etaZ b E := hη
  have hU := RawTag.rawUpdate_holds b E hb0 hb hE1 hE2 W hW
  have hF := ae_farUpdate (E := E) hb0 hb hE1 hE2 hW
  have hH := ae_growth_isHermitian W b
  have hq := Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)
    (ν := Measure.pi fun _ : Fin np => circularVectorLaw (Fin W))
  rw [probedPathLaw]
  filter_upwards [hq.ae hU, hq.ae hF, hq.ae hH] with x hUx hFx hA n hn i k hi hk r
  have hi' : birth W τ i < n + 1 := by omega
  have hk' : birth W τ k < n + 1 := by omega
  -- the 𝒦 increments
  have hK : ∀ i k : Fin np, birth W τ i < n → birth W τ k < n →
      complexSourceData b E W (n + 1) τ m x 0 i k - complexSourceData b E W n τ m x 0 i k =
        massF m i k * bilinear (nearL b E W n (birth W τ i) x.1 (x.2 i)) (stepDelta b E W n x.1)
          (nearR b E W n (birth W τ k) x.1 (x.2 k)) := by
    intro i k hi hk
    rw [sourceK_eq b E (n + 1) τ m x hm i k (by omega) (by omega),
      sourceK_eq b E n τ m x hm i k hi hk,
      hUx n hn _ _ hi hk]
    ring
  have hz : conj (boundaryZ b E) - boundaryZ b E ≠ 0 := by
    rw [conj_boundaryZ_sub]
    have : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast hη'.ne'
    simp [this]
  have hM : complexSourceData b E W (n + 1) τ m x 1 i k - complexSourceData b E W n τ m x 1 i k =
      massF m i k * ((bilinear (nearL b E W n (birth W τ i) x.1 (x.2 i)) (stepDelta b E W n x.1)
          (nearR b E W n (birth W τ k) x.1 (x.2 k)) -
        star (bilinear (nearL b E W n (birth W τ k) x.1 (x.2 k)) (stepDelta b E W n x.1)
          (nearR b E W n (birth W τ i) x.1 (x.2 i)))) /
        (conj (boundaryZ b E) - boundaryZ b E)) := by
    rw [sourceM_eq b E hη' (n + 1) τ m x hA i k, sourceM_eq b E hη' n τ m x hA i k]
    have e1 := hK i k hi hk
    have e2 := hK k i hk hi
    rw [sub_eq_iff_eq_add] at e1 e2
    rw [e1, e2, star_add, star_mul', star_massF, massF_symm]
    field_simp
    ring
  -- the far Gram increments
  have hd : ∀ j : Fin np, birth W τ j < n →
      farL b E W (n + 1) (birth W τ j) x.1 (x.2 j) = farL b E W n (birth W τ j) x.1 (x.2 j) +
        shiftL (stepDelta b E W n x.1) (boundaryResolvent b E W n x.1)
          (nearL b E W n (birth W τ j) x.1 (x.2 j)) := fun j hj => by
    funext y; exact (hFx n hn _ hj (x.2 j) y).1
  have he : ∀ j : Fin np, birth W τ j < n →
      farR b E W (n + 1) (birth W τ j) x.1 (x.2 j) = farR b E W n (birth W τ j) x.1 (x.2 j) +
        shiftR (stepDelta b E W n x.1) (boundaryResolvent b E W n x.1)
          (nearR b E W n (birth W τ j) x.1 (x.2 j)) := fun j hj => by
    funext y; exact (hFx n hn _ hj (x.2 j) y).2
  fin_cases r
  · simp only [Fin.zero_eta, incAt, incTerm, Matrix.cons_val_zero]
    exact hK i k hi hk
  · simp only [Fin.mk_one, incAt, incTerm, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact hM
  · change complexSourceData b E W (n + 1) τ m x 2 i k - complexSourceData b E W n τ m x 2 i k =
      massF m i k * incAt b E W n τ 2 i k x
    rw [incAt, incTerm_two]
    rw [sourceB_eq b E (n + 1) τ m x hm i k hi' hk', sourceB_eq b E n τ m x hm i k hi hk,
      hd i hi, hd k hk, gramOf_add]
    rw [sub_eq_iff_eq_add] at hM
    rw [hM]
    ring
  · change complexSourceData b E W (n + 1) τ m x 3 i k - complexSourceData b E W n τ m x 3 i k =
      massF m i k * incAt b E W n τ 3 i k x
    rw [incAt, incTerm_three]
    rw [sourceJ_eq b E (n + 1) τ m x hA hm i k hi' hk', sourceJ_eq b E n τ m x hA hm i k hi hk,
      hd i hi, hd k hk, he i hi, he k hk, gramOf_add, gramOf_add]
    ring

end BlockBand.SourceProcess.LengthCont.OneLayer
