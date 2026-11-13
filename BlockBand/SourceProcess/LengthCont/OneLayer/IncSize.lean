module

public import BlockBand.SourceProcess.LengthCont.OneLayer.FreshInc

/-!
# Fresh size of `incTerm`

`DeltaHyp.incTerm_size`: under the hypotheses `DeltaHyp` on the one-layer increment, every
component of the increment term `incTerm` has the fresh size bound `FreshSize`, with constants
polynomial in a bound `N` on the vectors.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance
open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ} {F : Type*} [MeasurableSpace F] {ρ : Measure F} [IsProbabilityMeasure ρ]
  {Δ : F → Matrix (Fin W) (Fin W) ℂ} {m₀ s₀ : ℝ}

theorem sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  have h := Real.sq_sqrt hx
  nlinarith [Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1)]

/-- The far-Gram increment `gramInc d d' (shiftL a) (shiftL a')`. -/
theorem DeltaHyp.dFd_size (h : DeltaHyp ρ Δ m₀ s₀) (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (aI aK dI dK : Fin W → ℂ) {N : ℝ} (hN : 0 ≤ N) (haI : vecNorm aI ≤ N)
    (haK : vecNorm aK ≤ N) (hdI : vecNorm dI ≤ N) (hdK : vecNorm dK ≤ N) :
    FreshSize ρ (fun f => gramInc dI dK (shiftL (Δ f) R aI) (shiftL (Δ f) R aK))
      ((2 * m₀ + (m₀ + s₀) ^ 2) * N ^ 2 * (1 + hsA R + hsB R))
      ((2 * s₀ + 2 * (m₀ + s₀) ^ 2) * N ^ 2 * (1 + hsA R + hsB R)) := by
  have hm := h.m_nonneg; have hs := h.s_nonneg
  have hA := hsA_nonneg R; have hB := hsB_nonneg R
  set H := 1 + hsA R + hsB R
  have hsq : Real.sqrt (hsA R) ≤ H := (sqrt_le_one_add hA).trans (by simp only [H]; linarith)
  have hAH : hsA R ≤ H := by simp only [H]; linarith
  have hvI : vecNorm (vL R dI) ≤ N * H :=
    (vecNorm_vL_le R dI).trans (mul_le_mul hdI hsq (Real.sqrt_nonneg _) hN)
  have hvK : vecNorm (vL R dK) ≤ N * H :=
    (vecNorm_vL_le R dK).trans (mul_le_mul hdK hsq (Real.sqrt_nonneg _) hN)
  have h0 := vecNorm_nonneg aI; have h1 := vecNorm_nonneg aK
  have h2 := vecNorm_nonneg (vL R dI); have h3 := vecNorm_nonneg (vL R dK)
  -- linear parts
  have s1 := (h.lin_size aK (vL R dI)).starC.mono (α' := m₀ * N ^ 2 * H) (σ' := s₀ * N ^ 2 * H)
    (by calc m₀ * vecNorm aK * vecNorm (vL R dI) ≤ m₀ * N * (N * H) := by gcongr
          _ = m₀ * N ^ 2 * H := by ring)
    (by calc s₀ * vecNorm aK * vecNorm (vL R dI) ≤ s₀ * N * (N * H) := by gcongr
          _ = s₀ * N ^ 2 * H := by ring)
  have s2 := (h.lin_size aI (vL R dK)).mono (α' := m₀ * N ^ 2 * H) (σ' := s₀ * N ^ 2 * H)
    (by calc m₀ * vecNorm aI * vecNorm (vL R dK) ≤ m₀ * N * (N * H) := by gcongr
          _ = m₀ * N ^ 2 * H := by ring)
    (by calc s₀ * vecNorm aI * vecNorm (vL R dK) ≤ s₀ * N * (N * H) := by gcongr
          _ = s₀ * N ^ 2 * H := by ring)
  -- quadratic part
  set r : Fin W → Fin W → ℂ := fun y x => R (0, x) (1, y)
  have hq := quad_size (ρ := ρ) (fun y f => shiftL (Δ f) R aI y) (fun y f => shiftL (Δ f) R aK y)
    (fun y => (h.meas_bilinear aI (r y)).star) (fun y => (h.meas_bilinear aK (r y)).star)
    (fun y => (m₀ + s₀) * vecNorm aI * vecNorm (r y))
    (fun y => (m₀ + s₀) * vecNorm aK * vecNorm (r y))
    (fun y => by have := vecNorm_nonneg (r y); positivity)
    (fun y => by have := vecNorm_nonneg (r y); positivity)
    (fun y => by rw [show (fun f => shiftL (Δ f) R aI y) =
        fun f => star (bilinear aI (Δ f) (r y)) from rfl, eLpNorm_star_fun]
                 exact h.lin_L4 aI (r y))
    (fun y => by rw [show (fun f => shiftL (Δ f) R aK y) =
        fun f => star (bilinear aK (Δ f) (r y)) from rfl, eLpNorm_star_fun]
                 exact h.lin_L4 aK (r y))
    (c := (m₀ + s₀) ^ 2 * N ^ 2 * H) (by positivity) (by
      have e : ∑ y, (m₀ + s₀) * vecNorm aI * vecNorm (r y) *
          ((m₀ + s₀) * vecNorm aK * vecNorm (r y)) =
          (m₀ + s₀) ^ 2 * vecNorm aI * vecNorm aK * hsA R := by
        rw [← sum_col_sq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
      rw [e]
      calc (m₀ + s₀) ^ 2 * vecNorm aI * vecNorm aK * hsA R ≤ (m₀ + s₀) ^ 2 * N * N * H := by
            gcongr
        _ = (m₀ + s₀) ^ 2 * N ^ 2 * H := by ring)
  have hsum := (s1.add s2).add hq
  have efun : (fun f => gramInc dI dK (shiftL (Δ f) R aI) (shiftL (Δ f) R aK)) =
      fun f => star (bilinear aK (Δ f) (vL R dI)) + bilinear aI (Δ f) (vL R dK) +
        ∑ y, star (shiftL (Δ f) R aI y) * shiftL (Δ f) R aK y := by
    funext f; rw [gramInc, gram_shiftL_left, gram_shiftL_right]; rfl
  rw [efun]
  exact hsum.mono (le_of_eq (by ring)) (le_of_eq (by ring))

/-- The scattered far-Gram increment `gramInc e e' (shiftR c) (shiftR c')`. -/
theorem DeltaHyp.dFe_size (h : DeltaHyp ρ Δ m₀ s₀) (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (cI cK eI eK : Fin W → ℂ) {N : ℝ} (hN : 0 ≤ N) (hcI : vecNorm cI ≤ N)
    (hcK : vecNorm cK ≤ N) (heI : vecNorm eI ≤ N) (heK : vecNorm eK ≤ N) :
    FreshSize ρ (fun f => gramInc eI eK (shiftR (Δ f) R cI) (shiftR (Δ f) R cK))
      ((2 * m₀ + (m₀ + s₀) ^ 2) * N ^ 2 * (1 + hsA R + hsB R))
      ((2 * s₀ + 2 * (m₀ + s₀) ^ 2) * N ^ 2 * (1 + hsA R + hsB R)) := by
  have hm := h.m_nonneg; have hs := h.s_nonneg
  have hA := hsA_nonneg R; have hB := hsB_nonneg R
  set H := 1 + hsA R + hsB R
  have hsq : Real.sqrt (hsB R) ≤ H := (sqrt_le_one_add hB).trans (by simp only [H]; linarith)
  have hvI : vecNorm (uR R eI) ≤ N * H :=
    (vecNorm_uR_le R eI).trans (mul_le_mul heI hsq (Real.sqrt_nonneg _) hN)
  have hvK : vecNorm (uR R eK) ≤ N * H :=
    (vecNorm_uR_le R eK).trans (mul_le_mul heK hsq (Real.sqrt_nonneg _) hN)
  have h0 := vecNorm_nonneg cI; have h1 := vecNorm_nonneg cK
  have h2 := vecNorm_nonneg (uR R eI); have h3 := vecNorm_nonneg (uR R eK)
  have s1 := (h.lin_size (uR R eI) cK).mono (α' := m₀ * N ^ 2 * H) (σ' := s₀ * N ^ 2 * H)
    (by calc m₀ * vecNorm (uR R eI) * vecNorm cK ≤ m₀ * (N * H) * N := by gcongr
          _ = m₀ * N ^ 2 * H := by ring)
    (by calc s₀ * vecNorm (uR R eI) * vecNorm cK ≤ s₀ * (N * H) * N := by gcongr
          _ = s₀ * N ^ 2 * H := by ring)
  have s2 := (h.lin_size (uR R eK) cI).starC.mono (α' := m₀ * N ^ 2 * H) (σ' := s₀ * N ^ 2 * H)
    (by calc m₀ * vecNorm (uR R eK) * vecNorm cI ≤ m₀ * (N * H) * N := by gcongr
          _ = m₀ * N ^ 2 * H := by ring)
    (by calc s₀ * vecNorm (uR R eK) * vecNorm cI ≤ s₀ * (N * H) * N := by gcongr
          _ = s₀ * N ^ 2 * H := by ring)
  set sv : Fin W → Fin W → ℂ := fun y x => star (R (1, y) (0, x))
  have hq := quad_size (ρ := ρ) (fun y f => shiftR (Δ f) R cI y) (fun y f => shiftR (Δ f) R cK y)
    (fun y => h.meas_bilinear (sv y) cI) (fun y => h.meas_bilinear (sv y) cK)
    (fun y => (m₀ + s₀) * vecNorm (sv y) * vecNorm cI)
    (fun y => (m₀ + s₀) * vecNorm (sv y) * vecNorm cK)
    (fun y => by have := vecNorm_nonneg (sv y); positivity)
    (fun y => by have := vecNorm_nonneg (sv y); positivity)
    (fun y => h.lin_L4 (sv y) cI) (fun y => h.lin_L4 (sv y) cK)
    (c := (m₀ + s₀) ^ 2 * N ^ 2 * H) (by positivity) (by
      have e : ∑ y, (m₀ + s₀) * vecNorm (sv y) * vecNorm cI *
          ((m₀ + s₀) * vecNorm (sv y) * vecNorm cK) =
          (m₀ + s₀) ^ 2 * vecNorm cI * vecNorm cK * hsB R := by
        rw [← sum_row_sq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
      rw [e]
      have hBH : hsB R ≤ H := by simp only [H]; linarith
      calc (m₀ + s₀) ^ 2 * vecNorm cI * vecNorm cK * hsB R ≤ (m₀ + s₀) ^ 2 * N * N * H := by
            gcongr
        _ = (m₀ + s₀) ^ 2 * N ^ 2 * H := by ring)
  have hsum := (s1.add s2).add hq
  have efun : (fun f => gramInc eI eK (shiftR (Δ f) R cI) (shiftR (Δ f) R cK)) =
      fun f => bilinear (uR R eI) (Δ f) cK + star (bilinear (uR R eK) (Δ f) cI) +
        ∑ y, star (shiftR (Δ f) R cI y) * shiftR (Δ f) R cK y := by
    funext f; rw [gramInc, gram_shiftR_left, gram_shiftR_right]; rfl
  rw [efun]
  exact hsum.mono (le_of_eq (by ring)) (le_of_eq (by ring))

/-- **Fresh size of every component of the increment.** -/
theorem DeltaHyp.incTerm_size (h : DeltaHyp ρ Δ m₀ s₀) (b E : ℝ)
    (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (aI aK cI cK dI dK eI eK : Fin W → ℂ)
    {N : ℝ} (hN : 0 ≤ N) (haI : vecNorm aI ≤ N) (haK : vecNorm aK ≤ N) (hcI : vecNorm cI ≤ N)
    (hcK : vecNorm cK ≤ N) (hdI : vecNorm dI ≤ N) (hdK : vecNorm dK ≤ N)
    (heI : vecNorm eI ≤ N) (heK : vecNorm eK ≤ N) (r : Fin 4) :
    FreshSize ρ (fun f => incTerm b E r (Δ f) R aI aK cI cK dI dK eI eK)
      ((4 + 2 * ‖(conj (boundaryZ b E) - boundaryZ b E)⁻¹‖) * (m₀ + (m₀ + s₀) ^ 2) * N ^ 2 *
        (1 + hsA R + hsB R))
      ((4 + 2 * ‖(conj (boundaryZ b E) - boundaryZ b E)⁻¹‖) * (s₀ + (m₀ + s₀) ^ 2) * N ^ 2 *
        (1 + hsA R + hsB R)) := by
  have hm := h.m_nonneg; have hs := h.s_nonneg
  have hA := hsA_nonneg R; have hB := hsB_nonneg R
  set H := 1 + hsA R + hsB R
  have hH : 1 ≤ H := by simp only [H]; linarith
  set ζ := (conj (boundaryZ b E) - boundaryZ b E)⁻¹
  have hζ := norm_nonneg ζ
  have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
  have hN2H : N ^ 2 ≤ N ^ 2 * H := le_mul_of_one_le_right hN2 hH
  have l1 := (h.lin_size aI cK).mono (α' := m₀ * N ^ 2) (σ' := s₀ * N ^ 2)
    (by have := vecNorm_nonneg aI; have := vecNorm_nonneg cK
        calc m₀ * vecNorm aI * vecNorm cK ≤ m₀ * N * N := by gcongr
          _ = m₀ * N ^ 2 := by ring)
    (by have := vecNorm_nonneg aI; have := vecNorm_nonneg cK
        calc s₀ * vecNorm aI * vecNorm cK ≤ s₀ * N * N := by gcongr
          _ = s₀ * N ^ 2 := by ring)
  have l2 := (h.lin_size aK cI).starC.mono (α' := m₀ * N ^ 2) (σ' := s₀ * N ^ 2)
    (by have := vecNorm_nonneg aK; have := vecNorm_nonneg cI
        calc m₀ * vecNorm aK * vecNorm cI ≤ m₀ * N * N := by gcongr
          _ = m₀ * N ^ 2 := by ring)
    (by have := vecNorm_nonneg aK; have := vecNorm_nonneg cI
        calc s₀ * vecNorm aK * vecNorm cI ≤ s₀ * N * N := by gcongr
          _ = s₀ * N ^ 2 := by ring)
  have t1 := (l1.sub l2).const_mul ζ
  have eT1 : (fun f => ζ * (bilinear aI (Δ f) cK - star (bilinear aK (Δ f) cI))) =
      fun f => (bilinear aI (Δ f) cK - star (bilinear aK (Δ f) cI)) /
        (conj (boundaryZ b E) - boundaryZ b E) := by
    funext f; rw [div_eq_inv_mul]
  rw [eT1] at t1
  have dFd := h.dFd_size R aI aK dI dK hN haI haK hdI hdK
  have dFe := h.dFe_size R cI cK eI eK hN hcI hcK heI heK
  have ht2 := sq_nonneg (m₀ + s₀)
  fin_cases r
  · refine l1.mono ?_ ?_ <;> simp only [H] at hN2H ⊢ <;> nlinarith [mul_nonneg hζ hm,
      mul_nonneg hζ hs, mul_nonneg (mul_nonneg hζ ht2) hN2]
  · refine t1.mono ?_ ?_ <;> simp only [H] at hN2H ⊢ <;> nlinarith [mul_nonneg hζ hm,
      mul_nonneg hζ hs, mul_nonneg (mul_nonneg hζ ht2) hN2, mul_nonneg (mul_nonneg hζ hm) hN2,
      mul_nonneg (mul_nonneg hζ hs) hN2, mul_nonneg ht2 hN2]
  · have t := t1.sub dFd
    refine t.mono ?_ ?_ <;> simp only [H] at hN2H ⊢ <;> nlinarith [mul_nonneg hζ hm,
      mul_nonneg hζ hs, mul_nonneg (mul_nonneg hζ ht2) hN2, mul_nonneg (mul_nonneg hζ hm) hN2,
      mul_nonneg (mul_nonneg hζ hs) hN2, mul_nonneg ht2 hN2,
      mul_nonneg (mul_nonneg hζ hm) (sub_nonneg.mpr hN2H),
      mul_nonneg (mul_nonneg hζ hs) (sub_nonneg.mpr hN2H)]
  · have t := dFd.sub dFe
    have hH0 : (0 : ℝ) ≤ 1 + hsA R + hsB R := by linarith
    refine t.mono ?_ ?_ <;> simp only [H] at hN2H ⊢ <;> nlinarith [mul_nonneg hζ hm,
      mul_nonneg hζ hs, mul_nonneg (mul_nonneg hζ ht2) hN2, mul_nonneg ht2 hN2,
      mul_nonneg (mul_nonneg (mul_nonneg hζ ht2) hN2) hH0,
      mul_nonneg (mul_nonneg (mul_nonneg hζ hm) hN2) hH0,
      mul_nonneg (mul_nonneg (mul_nonneg hζ hs) hN2) hH0]

end BlockBand.SourceProcess.LengthCont.OneLayer
