module

public import BlockBand.SourceProcess.LengthCont.OneLayer.IncSize
public import BlockBand.SourceProcess.LengthCont.OneLayer.HSTrace
public import BlockBand.SourceProcess.LengthCont.Pin
public import BlockBand.SourceProcess.RawTag.JointLaw
public import BlockBand.SourceProcess.FullSource.WardNoise
public import BlockBand.SourceProcess.RawTag.BirthTools

/-!
# The increment of a source coordinate as a function of (past, tags, fresh layer)

`incFun … ω g y` is the real (`s = true`) or imaginary part of `μ_{ik} · incTerm r` built from
the length-`n` frames of the growth sample `ω` with tags `g`, and the fresh layer `y`.
`incPast` is the same on `(PastSample × tags) × LayerSample`, through `extendPast`. A.s. on
`probedPathLaw`, `incr (sourceCoord …) n = incPast (π x, φ x)` with `π x = (pastCoords, tags)`,
`φ x = freshSample` (`ae_incr_eq_incPast`); `incPast` is measurable (`measurable_incPast`).
Frame bounds: `‖a‖, ‖c‖, ‖d‖, ‖e‖ ≤ ‖f‖` for Hermitian blocks (`vecNorm_parts_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.RawTag BlockBand.SourceProcess.ComplexSourceLaw
open scoped Matrix ComplexOrder ComplexConjugate

variable {W : ℕ}

/-- Real (`true`) or imaginary (`false`) part. -/
def part (s : Bool) (z : ℂ) : ℝ := if s then z.re else z.im

theorem abs_part_le (s : Bool) (z : ℂ) : |part s z| ≤ ‖z‖ := by
  cases s
  · exact Complex.abs_im_le_norm z
  · exact Complex.abs_re_le_norm z

theorem part_sub (s : Bool) (z w : ℂ) : part s (z - w) = part s z - part s w := by
  cases s <;> simp [part]

theorem measurable_part (s : Bool) : Measurable (part s) := by
  cases s
  · exact Complex.measurable_im
  · exact Complex.measurable_re

theorem integral_part {F : Type*} [MeasurableSpace F] {ρ : Measure F} (s : Bool) {X : F → ℂ}
    (hX : Integrable X ρ) : ∫ y, part s (X y) ∂ρ = part s (∫ y, X y ∂ρ) := by
  cases s
  · simp only [part, Bool.false_eq_true, ↓reduceIte]; exact integral_im hX
  · simp only [part, ↓reduceIte]; exact integral_re hX

theorem sourceCoord_incr {np : ℕ} (b E : ℝ) (W : ℕ) (τ m : Fin np → ℝ) (r : Fin 4)
    (i k : Fin np) (s : Bool) (n : ℕ) (x : ProbedPath W np) :
    incr (sourceCoord b E W τ m r i k s) n x = part s (complexSourceData b E W (n + 1) τ m x r i k -
      complexSourceData b E W n τ m x r i k) := by
  cases s <;> simp [incr, sourceCoord, part]

/-- The increment built from a growth sample, tags and a fresh layer. -/
def incFun {np : ℕ} (b E : ℝ) (W n : ℕ) (τ m : Fin np → ℝ) (r : Fin 4) (i k : Fin np)
    (s : Bool) (ω : GrowthPath W) (g : Fin np → Fin W → ℂ) (y : LayerSample W .oneBlockOnePort) :
    ℝ :=
  part s (massF m i k * incTerm b E r (freshDelta b E (pathX b E W n ω) y)
    (boundaryResolvent b E W n ω)
    (nearL b E W n (birth W τ i) ω (g i)) (nearL b E W n (birth W τ k) ω (g k))
    (nearR b E W n (birth W τ i) ω (g i)) (nearR b E W n (birth W τ k) ω (g k))
    (farL b E W n (birth W τ i) ω (g i)) (farL b E W n (birth W τ k) ω (g k))
    (farR b E W n (birth W τ i) ω (g i)) (farR b E W n (birth W τ k) ω (g k)))

/-- `incFun` on (past × tags) × fresh. -/
def incPast {np : ℕ} (b E : ℝ) (W n : ℕ) (τ m : Fin np → ℝ) (r : Fin 4) (i k : Fin np)
    (s : Bool) (z : (PastSample W n × (Fin np → Fin W → ℂ)) × LayerSample W .oneBlockOnePort) :
    ℝ :=
  incFun b E W n τ m r i k s (extendPast z.1.1) z.1.2 z.2

theorem measurable_incTerm {α : Type*} [MeasurableSpace α] (b E : ℝ) (r : Fin 4)
    {Δ : α → Matrix (Fin W) (Fin W) ℂ} {R : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {aI aK cI cK dI dK eI eK : α → Fin W → ℂ} (hΔ : ∀ x y, Measurable fun z => Δ z x y)
    (hR : ∀ x y, Measurable fun z => R z x y) (h1 : ∀ x, Measurable fun z => aI z x)
    (h2 : ∀ x, Measurable fun z => aK z x) (h3 : ∀ x, Measurable fun z => cI z x)
    (h4 : ∀ x, Measurable fun z => cK z x) (h5 : ∀ x, Measurable fun z => dI z x)
    (h6 : ∀ x, Measurable fun z => dK z x) (h7 : ∀ x, Measurable fun z => eI z x)
    (h8 : ∀ x, Measurable fun z => eK z x) :
    Measurable fun z => incTerm b E r (Δ z) (R z) (aI z) (aK z) (cI z) (cK z) (dI z) (dK z)
      (eI z) (eK z) := by
  fin_cases r <;>
    simp only [incTerm, gramInc, gramOf, shiftL, shiftR, bilinear, dotProduct, Matrix.mulVec,
      Pi.star_apply] <;> fun_prop

theorem measurable_farL {α : Type*} [MeasurableSpace α] (b E : ℝ) (l β : ℕ)
    {ω : α → GrowthPath W} {g : α → Fin W → ℂ} (hω : Measurable ω) (hg : Measurable g)
    (y : Fin W) : Measurable fun a => farL b E W l β (ω a) (g a) y :=
  (measurable_pi_apply _).comp (measurable_frame b E l β hω hg)

theorem measurable_farR {α : Type*} [MeasurableSpace α] (b E : ℝ) (l β : ℕ)
    {ω : α → GrowthPath W} {g : α → Fin W → ℂ} (hω : Measurable ω) (hg : Measurable g)
    (y : Fin W) : Measurable fun a => farR b E W l β (ω a) (g a) y :=
  (measurable_pi_apply _).comp (measurable_mulVec'
    ((BlockBand.SourceProcess.FullSourceStops.measurable_scatteringMatrix b E l).comp hω)
    (measurable_frame b E l β hω hg))

theorem measurable_incFun {np : ℕ} (b E : ℝ) (W n : ℕ) (τ m : Fin np → ℝ) (r : Fin 4)
    (i k : Fin np) (s : Bool) {α : Type*} [MeasurableSpace α] {ω : α → GrowthPath W}
    {g : α → Fin np → Fin W → ℂ} {y : α → LayerSample W .oneBlockOnePort} (hω : Measurable ω)
    (hg : Measurable g) (hy : Measurable y) :
    Measurable fun a => incFun b E W n τ m r i k s (ω a) (g a) (y a) := by
  have hgi : Measurable fun a => g a i := (measurable_pi_apply i).comp hg
  have hgk : Measurable fun a => g a k := (measurable_pi_apply k).comp hg
  have hX := (BlockBand.Transmission.PathJet.measurable_pathX b E n).comp hω
  have hD := BlockBand.SourceProcess.FullSource.measurable_freshDelta_comp b E hX hy
  have hR : Measurable fun a => boundaryResolvent b E W n (ω a) :=
    Measurable.of_eval_matrix _ fun _ _ =>
      ((BlockBand.SourceProcess.FullSourceStops.measurable_fullInverse b E n).comp hω).eval_matrix
  refine (measurable_part s).comp (measurable_const.mul (measurable_incTerm b E r
    (fun x y => hD.eval_matrix) (fun x y => hR.eval_matrix) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_))
  · exact fun x => (measurable_pi_apply x).comp (measurable_nearL b E n _ hω hgi)
  · exact fun x => (measurable_pi_apply x).comp (measurable_nearL b E n _ hω hgk)
  · exact fun x => (measurable_pi_apply x).comp (measurable_nearR b E n _ hω hgi)
  · exact fun x => (measurable_pi_apply x).comp (measurable_nearR b E n _ hω hgk)
  · exact fun x => measurable_farL b E n _ hω hgi x
  · exact fun x => measurable_farL b E n _ hω hgk x
  · exact fun x => measurable_farR b E n _ hω hgi x
  · exact fun x => measurable_farR b E n _ hω hgk x

theorem measurable_incPast {np : ℕ} (b E : ℝ) (W n : ℕ) (τ m : Fin np → ℝ) (r : Fin 4)
    (i k : Fin np) (s : Bool) : Measurable (incPast b E W n τ m r i k s) :=
  measurable_incFun b E W n τ m r i k s
    ((measurable_extendPast n).comp (measurable_fst.comp measurable_fst))
    (measurable_snd.comp measurable_fst) measurable_snd

theorem boundaryResolvent_extendPast (b E : ℝ) (l : ℕ) (ω : GrowthPath W) :
    boundaryResolvent b E W l (pastExt W l ω) = boundaryResolvent b E W l ω := by
  rw [boundaryResolvent, boundaryResolvent, fullInverse_extendPast]

theorem farL_extendPast (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) :
    farL b E W l β (pastExt W l ω) g = farL b E W l β ω g := by
  unfold farL; rw [frame_extendPast]

theorem farR_extendPast (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) :
    farR b E W l β (pastExt W l ω) g = farR b E W l β ω g := by
  unfold farR; rw [frame_extendPast, scatteringMatrix_extendPast]

/-- `incFun` at the extended past equals `incFun` at the sample. -/
theorem incFun_extendPast {np : ℕ} (b E : ℝ) (W n : ℕ) (τ m : Fin np → ℝ) (r : Fin 4)
    (i k : Fin np) (s : Bool) (ω : GrowthPath W) (g : Fin np → Fin W → ℂ)
    (y : LayerSample W .oneBlockOnePort) :
    incFun b E W n τ m r i k s (pastExt W n ω) g y = incFun b E W n τ m r i k s ω g y := by
  simp only [incFun, pathX_extendPast, boundaryResolvent_extendPast, nearL_extendPast,
    nearR_extendPast, farL_extendPast, farR_extendPast]

/-- **The increment is `incPast` of (past, tags, fresh)**, a.s. -/
theorem ae_incr_eq_incPast {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) {W : ℕ} (hW : 1 ≤ W) {np : ℕ} (τ m : Fin np → ℝ) (hm : ∀ j, 0 ≤ m j)
    {n : ℕ} (hn : 1 ≤ n) (hβ : ∀ j, birth W τ j < n) (r : Fin 4) (i k : Fin np) (s : Bool) :
    incr (sourceCoord b E W τ m r i k s) n =ᵐ[probedPathLaw W np b]
      fun x => incPast b E W n τ m r i k s ((pastCoords W n x.1, x.2), freshSample W n x.1) := by
  filter_upwards [ae_incr_eq hb0 hb hE1 hE2 hW τ m hm] with x hx
  rw [sourceCoord_incr, hx n hn i k (hβ i) (hβ k) r, incPast,
    show extendPast (pastCoords W n x.1) = pastExt W n x.1 from rfl, incFun_extendPast]
  rfl

/-!
## Frame-part bounds
-/

theorem vecNorm_far_le (u : Fin 2 × Fin W → ℂ) : vecNorm (fun y => u (1, y)) ≤ vecNorm u := by
  refine Real.sqrt_le_sqrt ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have : 0 ≤ ∑ y, ‖u (0, y)‖ ^ 2 := by positivity
  linarith

theorem isHermitian_extendPast {l : ℕ} {q : PastSample W l} (hq : q ∈ hermPast W l) :
    ∀ k, ((extendPast q).1 k).IsHermitian := by
  intro k
  simp only [extendPast]
  split_ifs with h
  · exact hq ⟨k, h⟩
  · exact Matrix.isHermitian_zero

/-- `‖a‖, ‖c‖, ‖d‖, ‖e‖ ≤ ‖f‖` (Hermitian blocks). -/
theorem vecNorm_parts_le (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    vecNorm (nearL b E W l β ω g) ≤ vecNorm (frame b E W l β ω g) ∧
      vecNorm (nearR b E W l β ω g) ≤ vecNorm (frame b E W l β ω g) ∧
      vecNorm (farL b E W l β ω g) ≤ vecNorm (frame b E W l β ω g) ∧
      vecNorm (farR b E W l β ω g) ≤ vecNorm (frame b E W l β ω g) := by
  have hU := vecNorm_mulVec_unitary _ (conjTranspose_mul_scattering b E l ω hA)
    (frame b E W l β ω g)
  refine ⟨BlockBand.SourceProcess.FullSource.vecNorm_nearSel_mulVec_le _,
    (BlockBand.SourceProcess.FullSource.vecNorm_nearSel_mulVec_le _).trans hU.le,
    vecNorm_far_le _, (vecNorm_far_le _).trans hU.le⟩

end BlockBand.SourceProcess.LengthCont.OneLayer
