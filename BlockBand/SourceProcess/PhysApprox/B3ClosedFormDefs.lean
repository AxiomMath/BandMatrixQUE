module

public import BlockBand.SourceProcess.PhysApprox.B3ModulAdapt
public import BlockBand.SourceProcess.PhysApprox.B3MartMax
public import BlockBand.SourceProcess.PhysApprox.ClosingAnalyticAlg
public import BlockBand.SourceProcess.RawTag.JointLaw

/-!
# The closed one-port input and the closed near frames (definitions)

At length `j`, phase `z`, with the unclosed port resolvent `ℝ_j`, scattering matrix `𝕊_j`, probe
frame `V_j = 𝒰_j*𝒥` and the closing map `C_j(z) = (1-A) + (1-zN_j)⁻¹zΠ𝕊_j(1-A)`:

* `closedNearR`: the closed near resolvent `R_cl = ι*ℝ_jC_j(z)ι` (near block of the Woodbury
  closed port resolvent);
* **`closedNearX`**: the closed one-port input `X_cl = z_∂ - R_cl⁻¹` (near-end Schur complement of
  the far-closed path of length `j`); **`b3ClosedX`** is the same as a `ClosedInputFam`;
* `closedNearU`: the left near frame `ι*C_j(z)*V_je_k` (near rows of the closed frame);
* `closedNearV`: the right near frame `ι*𝕊_j(1 + Z_j(z))V_je_l`, `Z = z(1-zN)⁻¹Π𝕊` (near rows of
  the closed outgoing frame; **not** `ι*𝕊_clV_cl` with the closed port scattering `𝕊_cl`).

Here: their measurability and invariance under `b3Ext W i` for `n_s ≤ j ≤ i`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingAux BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.FullSourceStops

variable {W np : ℕ}

/-- The closed near resolvent `R_cl = ι*ℝ_jC_j(z)ι` at length `j`, phase `z`. -/
def closedNearR (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  nearSel W * boundaryResolvent b E W j ω * physClosingMapAt b E s h W j ω z * (nearSel W)ᴴ

/-- **The closed one-port input** `X_cl = z_∂ - R_cl⁻¹` at length `j`, phase `z`. -/
def closedNearX (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - (closedNearR b E s h W j ω z)⁻¹

/-- **The closed input family** (`ClosedInputFam`): `X_cl` at length `j` and phase `e^{iθ}`. -/
def b3ClosedX (b E s h : ℝ) {np : ℕ} (_τ _m : Fin np → ℝ) (W j : ℕ) (y : ProbedPath W np × ℝ) :
    Matrix (Fin W) (Fin W) ℂ :=
  closedNearX b E s h W j y.1.1 (phase y.2)

/-- The closed resolvent factor `Z_j(z) = z(1 - zN_j)⁻¹Π𝕊_j` with the time-`s` closing data. -/
def physClosingZAt (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  closingZ (scatteringMatrix b E W j ω) (farEmbed (omittedProj b E h W (closeLen s W) ω))
    (farEmbed (closingPairing b E h W (closeLen s W) ω)) z

/-- Column `k` of the probe frame `V_j`. -/
def probeCol (b E : ℝ) (τ m : Fin np → ℝ) (W j : ℕ) (k : Fin np) (x : ProbedPath W np) :
    Fin 2 × Fin W → ℂ :=
  fun a => probeFrame b E W j τ m x a k

/-- The left closed near frame `u_k = ι*C_j(z)*V_je_k`. -/
def closedNearU (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ) (k : Fin np)
    (y : ProbedPath W np × ℝ) : Fin W → ℂ :=
  nearSel W *ᵥ ((physClosingMapAt b E s h W j y.1.1 (phase y.2))ᴴ *ᵥ
    probeCol b E τ m W j k y.1)

/-- The right closed near frame `v_l = ι*𝕊_j(1 + Z_j(z))V_je_l`. -/
def closedNearV (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ) (l : Fin np)
    (y : ProbedPath W np × ℝ) : Fin W → ℂ :=
  nearSel W *ᵥ (scatteringMatrix b E W j y.1.1 *ᵥ
    ((1 + physClosingZAt b E s h W j y.1.1 (phase y.2)) *ᵥ probeCol b E τ m W j l y.1))

/-!
## Measurability
-/

theorem measurable_boundaryResolvent_comp {α : Type*} [MeasurableSpace α] (b E : ℝ) (n : ℕ)
    {f : α → GrowthPath W} (hf : Measurable f) :
    Measurable fun a => boundaryResolvent b E W n (f a) :=
  Measurable.of_eval_matrix _ fun _ _ => ((measurable_fullInverse b E n).comp hf).eval_matrix

theorem measurable_closedNearR (b E s h : ℝ) (j : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ => closedNearR b E s h W j y.1.1 (phase y.2) :=
  measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_mul' measurable_const
    (measurable_boundaryResolvent_comp b E j (measurable_fst.comp measurable_fst)))
    (measurable_physClosingMapAt_comp b E s h j (measurable_fst.comp measurable_fst)
      (measurable_phase.comp measurable_snd))) measurable_const

theorem measurable_b3ClosedX (b E s h : ℝ) (τ m : Fin np → ℝ) (j : ℕ) :
    Measurable (b3ClosedX b E s h τ m W j) := by
  unfold b3ClosedX closedNearX
  exact measurable_matrix_sub measurable_const
    (measurable_matrix_inv.comp (measurable_closedNearR b E s h j))

theorem measurable_physClosingZAt_comp {α : Type*} [MeasurableSpace α] (b E s h : ℝ) (n : ℕ)
    {f : α → GrowthPath W} {z : α → ℂ} (hf : Measurable f) (hz : Measurable z) :
    Measurable fun a => physClosingZAt b E s h W n (f a) (z a) := by
  have hS := (measurable_scatteringMatrix b E n).comp hf
  have hA := measurable_farEmbed ((measurable_omittedProj b E h (closeLen s W)).comp hf)
  have hP := measurable_farEmbed ((measurable_closingPairing b E h (closeLen s W)).comp hf)
  unfold physClosingZAt closingZ closingN
  exact measurable_matrix_cmul hz (measurable_matrix_mul' (measurable_matrix_inv.comp
    (measurable_matrix_sub measurable_const (measurable_matrix_cmul hz
      (measurable_matrix_mul' (measurable_matrix_mul' hP hS) hA))))
    (measurable_matrix_mul' hP hS))

theorem measurable_probeCol (b E : ℝ) (τ m : Fin np → ℝ) (j : ℕ) (k : Fin np) :
    Measurable (probeCol b E τ m W j k) :=
  Measurable.of_eval fun _ => (measurable_probeFrame b E W j τ m).eval_matrix

theorem measurable_closedNearU (b E s h : ℝ) (τ m : Fin np → ℝ) (j : ℕ) (k : Fin np) :
    Measurable (closedNearU b E s h τ m W j k) :=
  RawTag.measurable_mulVec' measurable_const (RawTag.measurable_mulVec'
    (measurable_matrix_conjTranspose' (measurable_physClosingMapAt_comp b E s h j
      (measurable_fst.comp measurable_fst) (measurable_phase.comp measurable_snd)))
    ((measurable_probeCol b E τ m j k).comp measurable_fst))

theorem measurable_closedNearV (b E s h : ℝ) (τ m : Fin np → ℝ) (j : ℕ) (l : Fin np) :
    Measurable (closedNearV b E s h τ m W j l) :=
  RawTag.measurable_mulVec' measurable_const (RawTag.measurable_mulVec'
    ((measurable_scatteringMatrix b E j).comp (measurable_fst.comp measurable_fst))
    (RawTag.measurable_mulVec' (measurable_matrix_add measurable_const
      (measurable_physClosingZAt_comp b E s h j (measurable_fst.comp measurable_fst)
        (measurable_phase.comp measurable_snd)))
      ((measurable_probeCol b E τ m j l).comp measurable_fst)))

/-!
## Functions of the past
-/

variable {b E s h : ℝ} {τ m : Fin np → ℝ} {i j : ℕ}

theorem closedNearR_b3Ext (hs : closeLen s W ≤ j) (hji : j ≤ i) (y : ProbedPath W np × ℝ) :
    closedNearR b E s h W j (b3Ext W i y).1.1 (phase (b3Ext W i y).2) =
      closedNearR b E s h W j y.1.1 (phase y.2) := by
  simp only [b3Ext, closedNearR, boundaryResolvent, Modul.fullInverse_extPast b E hji,
    Modul.physClosingMapAt_extPast s h hs hji]

theorem b3ClosedX_b3Ext (hs : closeLen s W ≤ j) (hji : j ≤ i) (y : ProbedPath W np × ℝ) :
    b3ClosedX b E s h τ m W j (b3Ext W i y) = b3ClosedX b E s h τ m W j y := by
  simp only [b3ClosedX, closedNearX]
  rw [closedNearR_b3Ext hs hji]

theorem probeCol_b3Ext (hji : j ≤ i) (k : Fin np) (y : ProbedPath W np × ℝ) :
    probeCol b E τ m W j k (b3Ext W i y).1 = probeCol b E τ m W j k y.1 := by
  unfold probeCol probeFrame
  simp only [b3Ext, Modul.boundaryToInterior_extPast b E hji]

theorem physClosingZAt_b3Ext (hs : closeLen s W ≤ j) (hji : j ≤ i) (z : ℂ)
    (y : ProbedPath W np × ℝ) :
    physClosingZAt b E s h W j (b3Ext W i y).1.1 z = physClosingZAt b E s h W j y.1.1 z := by
  simp only [b3Ext, physClosingZAt, ClosedSumProof.scatteringMatrix_extPast hji,
    Modul.omittedProj_extPast b E h (hs.trans hji),
    Modul.closingPairing_extPast b E h (hs.trans hji)]

theorem closedNearU_b3Ext (hs : closeLen s W ≤ j) (hji : j ≤ i) (k : Fin np)
    (y : ProbedPath W np × ℝ) :
    closedNearU b E s h τ m W j k (b3Ext W i y) = closedNearU b E s h τ m W j k y := by
  have e := probeCol_b3Ext (b := b) (E := E) (τ := τ) (m := m) hji k y
  simp only [closedNearU, e]
  simp only [b3Ext, Modul.physClosingMapAt_extPast s h hs hji]

theorem closedNearV_b3Ext (hs : closeLen s W ≤ j) (hji : j ≤ i) (l : Fin np)
    (y : ProbedPath W np × ℝ) :
    closedNearV b E s h τ m W j l (b3Ext W i y) = closedNearV b E s h τ m W j l y := by
  have e := probeCol_b3Ext (b := b) (E := E) (τ := τ) (m := m) hji l y
  have eZ := physClosingZAt_b3Ext (b := b) (E := E) (s := s) (h := h) hs hji (phase y.2) y
  simp only [closedNearV, e]
  simp only [b3Ext] at eZ ⊢
  rw [eZ, ClosedSumProof.scatteringMatrix_extPast hji]

end BlockBand.SourceProcess.PhysApprox.B3
