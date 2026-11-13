module

public import BlockBand.SourceProcess.PhysApprox.B3JetNbhd

/-!
# The boundary-disc step of `ClosedShiftDiscTrace` (deterministic)

For passive inputs `X_c, X_o` and `|w - z_∂| ≤ η/2`, with `R = (z_∂ - X)⁻¹`, `G = (w - X)⁻¹` and
`M = 1 - (w - z_∂)G`: `‖G‖ ≤ 2/η`, `G = RM = MR`, so `G_c - G_o = M_c(R_c - R_o)M_o` and
`‖M‖ ≤ 2`. If `R_c - R_o = P diag(d) Q`, then

`|W⁻¹Tr(G_c - G_o)| ≤ 4W⁻¹ Σ_k |d_k| ‖Q_{k·}‖ ‖P_{·k}‖`   (**`stieltjes_sub_le_of_factor`**).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PathScalar
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `Tr(diag(d) A) = Σ_k d_k A_kk`. -/
theorem trace_diagonal_mul (d : Fin W → ℂ) (A : Matrix (Fin W) (Fin W) ℂ) :
    (diagonal d * A).trace = ∑ k, d k * A k k := by
  simp [Matrix.trace, diagonal_mul]

/-- `(QMP)_kk` as a bilinear form. -/
theorem mul_mul_apply_eq_bilinear (Q M P : Matrix (Fin W) (Fin W) ℂ) (k : Fin W) :
    (Q * M * P) k k = bilinear (fun i => star (Q k i)) M (fun j => P j k) := by
  simp only [bilinear, dotProduct, mulVec, Matrix.mul_apply, Pi.star_apply, star_star,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- The resolvent at the boundary parameter `w` on the disc: invertible, norm `≤ 2/η`. -/
theorem disc_resolvent {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {w : ℂ} (hw : ‖w - boundaryZ b E‖ ≤ etaZ b E / 2) :
    (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * (w • 1 - X)⁻¹ = 1 ∧
      (w • 1 - X)⁻¹ * (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X) = 1 ∧
      ‖(w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹‖ ≤ 2 / etaZ b E := by
  have him : w.im ≥ etaZ b E / 2 := by
    have h1 := Complex.abs_im_le_norm (w - boundaryZ b E)
    rw [Complex.sub_im] at h1
    have h2 := abs_le.1 (h1.trans hw)
    unfold etaZ at *
    linarith [h2.1]
  have hYp : (passiveY X + (w.im - etaZ b E / 2) • (1 : Matrix (Fin W) (Fin W) ℂ)).PosSemidef :=
    hY.add (Matrix.PosSemidef.one.smul (by linarith))
  have hK : matrixImaginaryPart (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X) =
      (passiveY X + (w.im - etaZ b E / 2) • 1) + (etaZ b E / 2) • 1 := by
    have h := matrixImaginaryPart_portPencil_general X w
    rw [portPencil] at h
    rw [h, passiveY, add_assoc, ← add_smul, sub_add_cancel]
    abel
  have hη2 : 0 < etaZ b E / 2 := by positivity
  obtain ⟨-, h1, h2⟩ := passive_inverse_constructed _ _ hη2 hYp hK
  refine ⟨h1, h2, ?_⟩
  have := norm_inv_le_of_im _ _ hη2 hYp hK
  rwa [inv_div] at this

/-- **The disc step**: from a factorization `R_c - R_o = P diag(d) Q`, the shift of
`W⁻¹Tr(w - X)⁻¹` on `|w - z_∂| ≤ η/2` is at most `4W⁻¹ Σ_k κ_k`. -/
theorem stieltjes_sub_le_of_factor {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) {Xc Xo : Matrix (Fin W) (Fin W) ℂ} (hc : (passiveY Xc).PosSemidef)
    (ho : (passiveY Xo).PosSemidef) {w : ℂ} (hw : ‖w - boundaryZ b E‖ ≤ etaZ b E / 2)
    {P Q : Matrix (Fin W) (Fin W) ℂ} {d : Fin W → ℂ}
    (hD : passiveResolvent b E Xc - passiveResolvent b E Xo = P * diagonal d * Q)
    {κ : Fin W → ℝ}
    (hκ : ∀ k, ‖d k‖ * vecNorm (fun i => star (Q k i)) * vecNorm (fun j => P j k) ≤ κ k) :
    ‖stieltjes Xc w - stieltjes Xo w‖ ≤ 4 / W * ∑ k, κ k := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  set c := w - boundaryZ b E with hcdef
  set ζ := boundaryZ b E with hζ
  -- the two resolvents at `z_∂`
  have hR : ∀ {X : Matrix (Fin W) (Fin W) ℂ}, (passiveY X).PosSemidef →
      (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * passiveResolvent b E X = 1 ∧
        passiveResolvent b E X * (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X) = 1 := by
    intro X hX
    have h := disc_resolvent (W := W) hη hX (w := ζ) (by rw [sub_self, norm_zero]; positivity)
    exact ⟨h.1, h.2.1⟩
  -- `G = R - c RG = R - c GR`
  have hGR : ∀ {X : Matrix (Fin W) (Fin W) ℂ}, (passiveY X).PosSemidef →
      (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ =
          passiveResolvent b E X * (1 - c • (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹) ∧
        (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ =
          (1 - c • (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹) * passiveResolvent b E X := by
    intro X hX
    obtain ⟨g1, g2, -⟩ := disc_resolvent (W := W) hη hX hw
    obtain ⟨r1, r2⟩ := hR hX
    set G := (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹
    set R := passiveResolvent b E X
    have hK : w • (1 : Matrix (Fin W) (Fin W) ℂ) - X = (ζ • 1 - X) + c • 1 := by
      rw [hcdef, sub_smul]; abel
    constructor
    · have : (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * G = 1 - c • G := by
        have := g1; rw [hK, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] at this
        exact eq_sub_of_add_eq this
      calc G = R * ((ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * G) := by
            rw [← Matrix.mul_assoc, r2, Matrix.one_mul]
        _ = R * (1 - c • G) := by rw [this]
    · have : G * (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X) = 1 - c • G := by
        have := g2; rw [hK, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at this
        exact eq_sub_of_add_eq this
      calc G = (G * (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)) * R := by
            rw [Matrix.mul_assoc, r1, Matrix.mul_one]
        _ = (1 - c • G) * R := by rw [this]
  set Gc := (w • (1 : Matrix (Fin W) (Fin W) ℂ) - Xc)⁻¹
  set Go := (w • (1 : Matrix (Fin W) (Fin W) ℂ) - Xo)⁻¹
  set Mc := 1 - c • Gc
  set Mo := 1 - c • Go
  have hdiff : Gc - Go = Mc * (P * diagonal d * Q) * Mo := by
    have e1 : Mc * passiveResolvent b E Xc = Gc := (hGR hc).2.symm
    have e2 : passiveResolvent b E Xo * Mo = Go := (hGR ho).1.symm
    have e0 : Gc - Go = Gc * Mo - Mc * Go := by
      simp only [Mc, Mo, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul]
      abel
    rw [← hD, e0, ← e1, ← e2]
    generalize Mc = A at *
    generalize Mo = B at *
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
  have hM : ∀ {G : Matrix (Fin W) (Fin W) ℂ}, ‖G‖ ≤ 2 / etaZ b E → ‖1 - c • G‖ ≤ 2 := by
    intro G hG
    calc ‖1 - c • G‖ ≤ ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖c‖ * ‖G‖ :=
          (norm_sub_le _ _).trans (by rw [norm_smul])
      _ ≤ 1 + etaZ b E / 2 * (2 / etaZ b E) := by
          gcongr
          · exact norm_one_matrix_le
      _ = 2 := by field_simp; ring
  have hMc := hM (disc_resolvent (W := W) hη hc hw).2.2
  have hMo := hM (disc_resolvent (W := W) hη ho hw).2.2
  have hMM : ‖Mo * Mc‖ ≤ 4 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg Mo])
  have ht : (Mc * (P * diagonal d * Q) * Mo).trace =
      (diagonal d * (Q * (Mo * Mc) * P)).trace := by
    rw [show Mc * (P * diagonal d * Q) * Mo = (Mc * P) * (diagonal d * (Q * Mo)) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm,
      show diagonal d * (Q * Mo) * (Mc * P) = diagonal d * (Q * (Mo * Mc) * P) by
        simp only [Matrix.mul_assoc]]
  have htr : stieltjes Xc w - stieltjes Xo w =
      (W : ℂ)⁻¹ * ∑ k, d k * (Q * (Mo * Mc) * P) k k := by
    rw [stieltjes, stieltjes, ← mul_sub, ← Matrix.trace_sub, ← trace_diagonal_mul, ← ht, ← hdiff]
  rw [htr, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ k, d k * (Q * (Mo * Mc) * P) k k‖ ≤ ∑ k, 4 * κ k := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, mul_mul_apply_eq_bilinear]
    have hb := norm_bilinear_le (fun i => star (Q k i)) (Mo * Mc) (fun j => P j k)
    have hv1 := vecNorm_nonneg (fun i => star (Q k i))
    have hv2 := vecNorm_nonneg (fun j => P j k)
    calc ‖d k‖ * ‖bilinear (fun i => star (Q k i)) (Mo * Mc) (fun j => P j k)‖
        ≤ ‖d k‖ * (vecNorm (fun i => star (Q k i)) * 4 * vecNorm (fun j => P j k)) := by
          gcongr
          exact hb.trans (by gcongr)
      _ = 4 * (‖d k‖ * vecNorm (fun i => star (Q k i)) * vecNorm (fun j => P j k)) := by ring
      _ ≤ 4 * κ k := by gcongr; exact hκ k
  rw [← Finset.mul_sum] at hsum
  calc (W : ℝ)⁻¹ * ‖∑ k, d k * (Q * (Mo * Mc) * P) k k‖ ≤ (W : ℝ)⁻¹ * (4 * ∑ k, κ k) := by
        gcongr
    _ = 4 / W * ∑ k, κ k := by ring

end BlockBand.SourceProcess.PhysApprox.B3.Jet
