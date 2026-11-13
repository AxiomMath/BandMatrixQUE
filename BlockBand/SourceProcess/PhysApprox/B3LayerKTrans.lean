module

public import BlockBand.SourceProcess.PhysApprox.B3LayerKSep
public import BlockBand.SourceProcess.PhysApprox.B3LayerKSepTr
public import BlockBand.Transmission.Bridge.TransportStep

/-!
# `B3PadTransport` from `B3PadInvertible`

The padded frame is transported by the fresh layer, `V_{pr,+} = N*V_pr`, given the hypothesis
`B3PadInvertible`.

* `b3OpenFrameAt_succ`: at a no-birth step the open frame is transported by the open fresh
  transport, `X_{j+1} = N_jᴴX_j` (current columns by `stepProd`; probe columns by
  `boundaryToInterior_succ`, born tags; unborn tags vanish at `j` and `j + 1`).
* **`b3PadTransport_of_inv : B3PadInvertible → B3PadTransport`**: with
  `closingMap_mul_freshTransport` (`C_j(1 - A)N(𝕏_pad) = N_jC_{j+1}(1 - A)`), taking adjoints and
  `C(1 - A) = C`: `V_{j+1} = C_{j+1}ᴴX_{j+1} = C_{j+1}ᴴN_jᴴX_j = N(𝕏_pad)ᴴC_jᴴX_j = N(𝕏_pad)ᴴV_j`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosedPath BlockBand.Transmission.Bridge
open BlockBand.Transmission
open BlockBand.SourceProcess.FullSourceStops

variable {W np K : ℕ}

/-- `C(z)(1 - A) = C(z)`. -/
theorem closingMap_mul_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {S A Pi : Matrix ι ι ℂ}
    (hA2 : A * A = A) (z : ℂ) : closingMap S A Pi z * (1 - A) = closingMap S A Pi z := by
  have h3 : (1 - A) * (1 - A) = 1 - A := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hA2]; simp
  rw [closingMap, closingT, Matrix.add_mul, h3, Matrix.mul_assoc, Matrix.smul_mul,
    Matrix.mul_assoc, Matrix.mul_assoc, h3]
  simp only [Matrix.mul_assoc]

/-- Reindexing the rows of `U` in `Uᴴv`. -/
theorem conjTranspose_mulVec_reindex {α β γ : Type*} [Fintype α] [Fintype γ]
    (U : Matrix α β ℂ) (e : γ ≃ α) (v : α → ℂ) :
    Uᴴ *ᵥ v = (U.submatrix e id)ᴴ *ᵥ (v ∘ e) := by
  funext i
  simp only [mulVec, dotProduct, conjTranspose_apply, submatrix_apply, id, Function.comp]
  exact (e.sum_comp fun x => star (U x i) * v x).symm

theorem fromRows_conjTranspose_mulVec_elim {m₁ m₂ n : Type*} [Fintype m₁] [Fintype m₂]
    (R₁ : Matrix m₁ n ℂ) (R₂ : Matrix m₂ n ℂ) (c : m₂ → ℂ) :
    (Matrix.fromRows R₁ R₂)ᴴ *ᵥ Sum.elim (0 : m₁ → ℂ) c = R₂ᴴ *ᵥ c := by
  funext i
  simp [mulVec, dotProduct, Fintype.sum_sum_type, conjTranspose_apply]

/-- **The open frame at a no-birth step is transported by the open fresh transport.** -/
theorem b3OpenFrameAt_succ (b E s : ℝ) (τ m : Fin np → ℝ) {j : ℕ} (hj1 : 1 ≤ j)
    (hjc : closeLen s W ≤ j) (hnb : ∀ k : Fin np, ⌊(W : ℝ) * τ k⌋₊ ≠ j)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (x : ProbedPath W np)
    (hA : ∀ k, (x.1.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W j x.1) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (j + 1) x.1) - (E : ℂ) • 1))
    (hB : IsUnit (x.1.2 (j + 1))) :
    b3OpenFrameAt b E s τ m W (j + 1) Vs x =
      (transportN b E W j x.1)ᴴ * b3OpenFrameAt b E s τ m W j Vs x := by
  ext a col
  rcases col with k | k
  · have hm : j + 1 - closeLen s W = (j - closeLen s W) + 1 := by omega
    have hm' : closeLen s W + (j - closeLen s W) = j := by omega
    have key : (stepProd (fun i => transportN b E W i x.1) (closeLen s W)
        (j + 1 - closeLen s W))ᴴ * Vs x.1 = (transportN b E W j x.1)ᴴ *
          ((stepProd (fun i => transportN b E W i x.1) (closeLen s W)
            (j - closeLen s W))ᴴ * Vs x.1) := by
      rw [hm, stepProd, hm', conjTranspose_mul, Matrix.mul_assoc]
    show ((stepProd (fun i => transportN b E W i x.1) (closeLen s W)
        (j + 1 - closeLen s W))ᴴ * Vs x.1) a k = _
    rw [key, Matrix.mul_apply, Matrix.mul_apply]
    rfl
  · show probeFrame b E W (j + 1) τ m x a k = _
    rw [Matrix.mul_apply]
    change _ = ∑ c, (transportN b E W j x.1)ᴴ a c * probeFrame b E W j τ m x c k
    by_cases hk : ⌊(W : ℝ) * τ k⌋₊ < j
    · have hPS : PassiveSample b E (fun _ => 0) x.1 := ⟨hA, fun _ => le_rfl, hη⟩
      obtain ⟨hU, -⟩ := boundaryToInterior_succ b E hj1 x.1 hA hη hF hF'
        (isUnit_freshLayer_path hPS j hB)
      have hcol : probeCol b E τ m W (j + 1) k x =
          (transportN b E W j x.1)ᴴ *ᵥ probeCol b E τ m W j k x := by
        rw [probeCol_eq, probeCol_eq, conjTranspose_mulVec_reindex _ (headEquiv j W), hU,
          probeColumns_comp_old τ m x.2 hk, fromRows_conjTranspose_mulVec_elim,
          conjTranspose_mul, ← mulVec_mulVec]
      have := congrFun hcol a
      simp only [probeCol, mulVec, dotProduct] at this
      exact this
    · have h1 : j + 1 ≤ ⌊(W : ℝ) * τ k⌋₊ := by have := hnb k; omega
      have h2 : j ≤ ⌊(W : ℝ) * τ k⌋₊ := by omega
      simp [probeFrame_dead b E τ m h1, probeFrame_dead b E τ m h2]

/-- **`B3PadTransport` from `B3PadInvertible`.** -/
theorem b3PadTransport_of_inv (hI : B3LayerMean.B3PadInvertible) :
    B3LayerMean.B3PadTransport := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb, hE1, hE2, hη, hh⟩ := B3LayerMean.frameDomain_facts hF
  have hb0 : 0 < b := hF.1.1
  have hηim : 0 < (boundaryZ b E).im := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  filter_upwards [hI b E np τ m T s h K Vs hF, eventually_ge_atTop 1,
    B3Cur.eventually_one_le_closeLen hF.2.1] with W hIW hW hs1 j hj
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
  have hj1 : 1 ≤ j := hs1.trans hjc
  have hnb : ∀ k : Fin np, ⌊(W : ℝ) * τ k⌋₊ ≠ j := fun k h' =>
    (Finset.mem_filter.mp hj).2 ⟨k, h'⟩
  have hZm := B3LayerMean.measurable_b3ChainXX (np := np) (W := W) b E s h j
  have hZinv : ∀ y : ProbedPath W np × ℝ, b3ChainXX b E s h W j (b3Ext W j y) =
      b3ChainXX b E s h W j y := fun y => B3LayerMean.b3ChainXX_b3Ext hjc le_rfl y
  filter_upwards [hIW j hjc, hIW (j + 1) (hjc.trans (Nat.le_succ j)),
    ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW, ae_closed_pathSchur_succ (np := np) hb hW E,
    ae_isUnit_freshPivot hb hW E j hZm hZinv,
    B3LayerMean.ae_closed_scattering_unitary (np := np) hb hE1 hE2 hW] with y h0 h1 hP hsucc
    hGp hSu _hyA
  obtain ⟨hA, hFp, hBd, -⟩ := hP
  set Y := pathSchur E (pathAt W j y.1.1) with hYdef
  have hsj := hsucc j hj1
  have hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Y) :=
    portPencil_isUnit _ (pathSchur_isHermitian E j y.1.1 hA) hηim
  have hKg : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      freshTwoPortSchur E Y (freshSample W j y.1.1)) := by
    rw [← hsj]
    exact portPencil_isUnit _ (pathSchur_isHermitian E (j + 1) y.1.1 hA) hηim
  have hG := isUnit_freshPivot_path E y.1.1 (hFp j) (hFp (j + 1))
  have hXH := (B3LayerMean.b3ChainXX_good τ m hη hh (hSu j) h0.1 h0.2).1
  have e0 := b3ChainXX_eq_cay b E s h W j y (hFp j)
  have hU := h0.1
  have hUg := h1.1
  have hV := h0.2
  rw [scatteringMatrix_eq b E j y.1.1 (hFp j)] at hU
  rw [scatteringMatrix_eq b E (j + 1) y.1.1 (hFp (j + 1)), hsj] at hUg
  rw [B3LayerMean.b3PadScatter_eq, scatteringMatrix_eq b E j y.1.1 (hFp j)] at hV
  rw [e0] at hGp hXH
  rw [e0]
  simp only [padScat_eq_padScatQ, farEmbed_conjTranspose] at hV hGp hXH ⊢
  have key := closingMap_mul_freshTransport b E hη (omittedProj_mul_self b E h _ _)
    (omittedProj_mul_closingPairing b E h _ _) (phase y.2) Y (freshSample W j y.1.1)
    (pathSchur_isHermitian E j y.1.1 hA) (hA j) (hBd (j + 1)) hK hKg hG hU hUg hV hXH hGp
  set A := farEmbed (omittedProj b E h W (closeLen s W) y.1.1) with hAdef
  have hA2 : A * A = A := by rw [hAdef, farEmbed_mul, omittedProj_mul_self]
  have hAH : Aᴴ = A := by rw [hAdef, farEmbed_conjTranspose, omittedProj_conjTranspose]
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) y.1.1) with hPidef
  have hfr := b3OpenFrameAt_succ b E s τ m hj1 hjc hnb (Vs W) y.1 hA hηim (hFp j) (hFp (j + 1))
    (hBd (j + 1))
  have hC0 : physClosingMapAt b E s h W j y.1.1 (phase y.2) =
      closingMap (twoPortScattering b E Y) A Pi (phase y.2) := by
    rw [physClosingMapAt, scatteringMatrix_eq b E j y.1.1 (hFp j)]
  have hC1 : physClosingMapAt b E s h W (j + 1) y.1.1 (phase y.2) =
      closingMap (twoPortScattering b E (freshTwoPortSchur E Y (freshSample W j y.1.1))) A Pi
        (phase y.2) := by
    rw [physClosingMapAt, scatteringMatrix_eq b E (j + 1) y.1.1 (hFp (j + 1)), hsj]
  have hadj := congrArg conjTranspose key
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hAH] at hadj
  have e0 := congrArg conjTranspose
    (closingMap_mul_one_sub (S := twoPortScattering b E Y) (Pi := Pi) hA2 (phase y.2))
  rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hAH] at e0
  have e1 := congrArg conjTranspose (closingMap_mul_one_sub
    (S := twoPortScattering b E (freshTwoPortSchur E Y (freshSample W j y.1.1))) (Pi := Pi) hA2
    (phase y.2))
  rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hAH] at e1
  rw [e0, ← Matrix.mul_assoc, e1] at hadj
  unfold b3ClosedFrameAt
  rw [hfr, hC0, hC1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hadj]

end BlockBand.SourceProcess.PhysApprox.B3
