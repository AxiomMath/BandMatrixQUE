module

public import BlockBand.Diffusion.Base.TransitionLawDefs

/-!
# The one-pair boundary dual and the Doob killed law: definitions

Local copies of the transmission-path and lifetime-bridge definitions used by the Doob transform:
* the dual chamber `dkDualChamber q` of ratio parameters, the dual generator `dkDualGenerator`
  and the associated martingales `dkDualMartingale`;
* `IsDkBoundaryDeletionPath`: càdlàg particle-number paths `n` that decrease by deleting the first
  particle when it reaches the corner `(0, 0)`, with continuous coordinates in between;
* `IsDkBoundaryDualProcess`: an adapted process with such paths from a dual start, solving the
  martingale problem for the dual generator in the chamber;
* `DkLbkCornerHeatIdentity D0`: for `w` in the strip, `w ≠ (0, 0)`,
  `∫ p_t(w, w') h(w') dw' + (D₀/2) ∫₀ᵗ p_s(w, (0, 0)) ds = h(w)`, `h(w) = (w₁ + w₂)⁻¹` (`dkHarm`);
* `DkLbkDoobKilledLaw D0`: before extinction, the finite-dimensional laws of the first particle of
  a one-pair boundary dual from `(x, y)` are the Doob transform
  `∏ p_{tᵢ - tᵢ₋₁}(zᵢ₋₁, zᵢ) · (x + y) h(z_k)` of the base kernel by `h`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-- Ordered ratio parameters `0 < x₁ < ⋯ < x_p`, `0 < y₁ < ⋯ < y_p < 1`. -/
def IsDkRatioParameter {p : ℕ} (x y : Fin p → ℝ) : Prop :=
  StrictMono x ∧ StrictMono y ∧ (∀ i, 0 < x i) ∧ ∀ i, 0 < y i ∧ y i < 1

/-- Dual coordinates `(x, y)` with `q` pairs. -/
abbrev DkDualCoord (q : ℕ) := (Fin q → ℝ) × (Fin q → ℝ)

/-- The ordered interior chamber `𝒞_q`:
`0 < x₁ < ⋯ < x_q`, `0 < y₁ < ⋯ < y_q < 1`.
-/
def dkDualChamber (q : ℕ) : Set (DkDualCoord q) :=
  {z | IsDkRatioParameter z.1 z.2}

/-- Unit direction `∂_{x_i}`. -/
def dkDirX {q : ℕ} (i : Fin q) : DkDualCoord q := (Pi.single i 1, 0)

/-- Unit direction `∂_{y_j}`. -/
def dkDirY {q : ℕ} (j : Fin q) : DkDualCoord q := (0, Pi.single j 1)

/-- `β_i^x = 1 + 2x_i + 2x_i(1+x_i)[Σ_{k≠i} (x_i-x_k)⁻¹ - Σ_j (x_i+y_j)⁻¹]`. -/
def dkDualDriftX {q : ℕ} (z : DkDualCoord q) (i : Fin q) : ℝ :=
  1 + 2 * z.1 i + 2 * z.1 i * (1 + z.1 i) *
    ((∑ k ∈ Finset.univ.erase i, 1 / (z.1 i - z.1 k)) - ∑ j, 1 / (z.1 i + z.2 j))

/-- `β_j^y = 1 - 2y_j + 2y_j(1-y_j)[Σ_{ℓ≠j} (y_j-y_ℓ)⁻¹ - Σ_i (x_i+y_j)⁻¹]`. -/
def dkDualDriftY {q : ℕ} (z : DkDualCoord q) (j : Fin q) : ℝ :=
  1 - 2 * z.2 j + 2 * z.2 j * (1 - z.2 j) *
    ((∑ l ∈ Finset.univ.erase j, 1 / (z.2 j - z.2 l)) - ∑ i, 1 / (z.1 i + z.2 j))

/-- The dual generator `𝒟_q`. -/
def dkDualGenerator (D0 : ℝ) {q : ℕ} (f : DkDualCoord q → ℝ) (z : DkDualCoord q) : ℝ :=
  D0 / 2 *
    ((∑ i, (z.1 i * (1 + z.1 i) * fderiv ℝ (fun w => fderiv ℝ f w (dkDirX i)) z (dkDirX i) +
        dkDualDriftX z i * fderiv ℝ f z (dkDirX i))) +
      ∑ j, (z.2 j * (1 - z.2 j) * fderiv ℝ (fun w => fderiv ℝ f w (dkDirY j)) z (dkDirY j) +
        dkDualDriftY z j * fderiv ℝ f z (dkDirY j)))

/-- The first `q` coordinates of sequences `x, y: ℕ → ℝ`. -/
def dkDualCoordOf (q : ℕ) (x y : ℕ → ℝ) : DkDualCoord q := (fun i => x i, fun i => y i)

/-- A level-`q` test function lifted to the whole state space (zero on other levels). -/
def dkDualLift {q : ℕ} (f : DkDualCoord q → ℝ) (n : ℕ) (x y : ℕ → ℝ) : ℝ :=
  if n = q then f (dkDualCoordOf q x y) else 0

/-- The extinction time `ζ = inf {t : N_t = 0}` (`⊤` if never). -/
def dkDualExtinction {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : N t ω = 0), (t : ℝ≥0∞)

/-- Entrance time into the levels `≤ q`. -/
def dkDualEntrance {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (q : ℕ) (ω : Ω) : ℝ≥0 :=
  sInf {t | N t ω ≤ q}

open scoped Classical in

/-- The value of a level-`q` test at the entrance into level `q`, once entered by time `t`. -/
def dkDualEntranceValue {Ω : Type*} {q : ℕ} (f : DkDualCoord q → ℝ) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ∃ u ≤ t, N u ω ≤ q then
    dkDualLift f (N (dkDualEntrance N q ω) ω) (X (dkDualEntrance N q ω) ω)
      (Y (dkDualEntrance N q ω) ω)
  else 0

/-- `f(Z_t) - f(Z_{σ_q}) 1{σ_q ≤ t} - ∫_0^t 𝒟_q f(Z_u) du` for a level-`q` test `f`. -/
def dkDualMartingale {Ω : Type*} (D0 : ℝ) (q : ℕ) (f : DkDualCoord q → ℝ) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  dkDualLift f (N t ω) (X t ω) (Y t ω) - dkDualEntranceValue f N X Y t ω -
    ∫ u in Set.Ioc (0 : ℝ) t,
      dkDualLift (dkDualGenerator D0 f) (N u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω)

/-- **Boundary starts**:
`0 ≤ x₁ < ⋯ < x_p`, `0 ≤ y₁ < ⋯ < y_p ≤ 1`, all `x_i + y_j > 0`.
-/
def IsDkDualStart {p : ℕ} (x y : Fin p → ℝ) : Prop :=
  StrictMono x ∧ StrictMono y ∧ (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
    ∀ i j, 0 < x i + y j

/-- Pathwise structure of the deletion process from a boundary start. -/
structure IsDkBoundaryDeletionPath (n : ℝ≥0 → ℕ) (x y : ℝ≥0 → ℕ → ℝ) : Prop where
  antitone : Antitone n
  chamber : ∀ t, 0 < t → dkDualCoordOf (n t) (x t) (y t) ∈ dkDualChamber (n t)
  rightCont : ∀ t, ∀ᶠ u in 𝓝[>] t, n u = n t
  cont : ∀ t₁ t₂, t₁ ≤ t₂ → n t₂ = n t₁ → ∀ i, i < n t₁ →
    ContinuousOn (fun u => x u i) (Set.Icc t₁ t₂) ∧ ContinuousOn (fun u => y u i) (Set.Icc t₁ t₂)
  deletion : ∀ τ : ℝ≥0, 0 < τ → ∀ q : ℕ, (∀ᶠ u in 𝓝[<] τ, n u = q + 1) → n τ ≠ q + 1 →
    n τ = q ∧ Tendsto (fun u => x u 0) (𝓝[<] τ) (𝓝 0) ∧
      Tendsto (fun u => y u 0) (𝓝[<] τ) (𝓝 0) ∧
      ∀ i, i < q → Tendsto (fun u => x u (i + 1)) (𝓝[<] τ) (𝓝 (x τ i)) ∧
        Tendsto (fun u => y u (i + 1)) (𝓝[<] τ) (𝓝 (y τ i))

/-- **The conservative deletion law started at a (possibly boundary) point `(x, y)`**: a copy of
`IsBoundaryDualProcess`. -/
structure IsDkBoundaryDualProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (D0 : ℝ) {p : ℕ}
    (x y : Fin p → ℝ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) : Prop where
  prob : IsProbabilityMeasure P
  adapted : ∀ t, Measurable[𝓖 t] (N t) ∧ Measurable[𝓖 t] (X t) ∧ Measurable[𝓖 t] (Y t)
  start : ∀ᵐ ω ∂P, N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i
  paths : ∀ᵐ ω ∂P, IsDkBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)
  martingale : ∀ q : ℕ, 1 ≤ q → q ≤ p → ∀ f : DkDualCoord q → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
    HasCompactSupport f → tsupport f ⊆ dkDualChamber q →
    Martingale (dkDualMartingale D0 q f N X Y) 𝓖 P

/-- The point `(X_s, Y_s)` of a one-pair dual realization at real time `s`. -/
def dkDualPoint {Ω : Type*} (X Y : ℝ≥0 → Ω → ℕ → ℝ) (s : ℝ) (ω : Ω) : ℝ × ℝ :=
  (X s.toNNReal ω 0, Y s.toNNReal ω 0)

/-- The last time `t_k` of `0 < t₁ < ⋯ < t_k` (`0` if `k = 0`). -/
def dkLastTime {k : ℕ} (ts : Fin k → ℝ) : ℝ := (Fin.cons 0 ts : Fin (k + 1) → ℝ) (Fin.last k)

/-- The last point `z_k` of `z₀ = z, z₁, …, z_k` (`z` if `k = 0`). -/
def dkLastPoint {α : Type*} (z : α) {k : ℕ} (zs : Fin k → α) : α :=
  (Fin.cons z zs : Fin (k + 1) → α) (Fin.last k)

/-- The string of transition densities `p_{t₁}(z, z₁) ⋯ p_{t_k - t_{k-1}}(z_{k-1}, z_k)`. -/
def dkFddProd {α : Type*} (p : ℝ → α → α → ℝ) (z : α) {k : ℕ} (ts : Fin k → ℝ)
    (zs : Fin k → α) : ℝ≥0∞ :=
  ∏ i : Fin k, ENNReal.ofReal
    (p (ts i - (Fin.cons 0 ts : Fin (k + 1) → ℝ) i.castSucc)
      ((Fin.cons z zs : Fin (k + 1) → α) i.castSucc) (zs i))

/-- The harmonic function `H(x, y) = (x + y)⁻¹` of the `H` transform. -/
def dkHarm (w : ℝ × ℝ) : ℝ := (w.1 + w.2)⁻¹

/-- **The corner heat identity** for the explicit kernel:
`∫ p_t(z,z′) H(z′) dz′ + (D₀/2) ∫_{(0,t]} p_s(z,(0,0)) ds = H(z)` for `z` in the closed strip,
`z ≠ (0,0)`, `t > 0`. Only its consequence `P_t H ≤ H` is used (to bound the duality functions).
It is proved as `dkLbkCornerHeatIdentity_holds`.
-/
def DkLbkCornerHeatIdentity (D0 : ℝ) : Prop :=
  ∀ w ∈ exBaseStrip, w ≠ (0, 0) → ∀ t : ℝ, 0 < t →
    (∫⁻ w', ENNReal.ofReal (exKernel D0 t w w') * ENNReal.ofReal (dkHarm w')) +
        ENNReal.ofReal (D0 / 2) * ∫⁻ s in Ioc 0 t, ENNReal.ofReal (exKernel D0 s w (0, 0)) =
      ENNReal.ofReal (dkHarm w)

open scoped Classical in

/-- **The killed finite-dimensional law** of every one-pair boundary dual from `z = (x, y)`:
`E[F(Z_{t₁}, …, Z_{t_k}); t_k < σ₀] = ∫ F(zs) p_{t₁}(z,z₁)⋯p_{t_k-t_{k-1}}(z_{k-1},z_k) (x+y) H(z_k)
dzs`.
-/
def DkLbkDoobKilledLaw (D0 : ℝ) : Prop :=
  ∀ x y : ℝ, IsDkDualStart ![x] ![y] →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y →
      ∀ (k : ℕ) (ts : Fin k → ℝ), StrictMono ts → (∀ i, 0 < ts i) →
        ∀ F : (Fin k → ℝ × ℝ) → ℝ≥0∞, Measurable F →
          ∫⁻ ω, (if ENNReal.ofReal (dkLastTime ts) < dkDualExtinction N ω
              then F (fun i => dkDualPoint X Y (ts i) ω) else 0) ∂P =
            ∫⁻ zs, F zs * dkFddProd (exKernel D0) (x, y) ts zs *
              ENNReal.ofReal ((x + y) * dkHarm (dkLastPoint (x, y) zs))

end BlockBand.Diffusion
